import KernelMultipliers
import CutoffConvolutionKernel
import GlobalSpectralQuotientTrace

open Filter Function InnerProductSpace MeasureTheory NumberField Set Topology
open scoped CompactlySupported ENNReal InnerProductSpace NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

/-- A measurable representative of an operator's Hilbert–Schmidt kernel. -/
def RepresentsL2Kernel {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k : X × X → ℂ) : Prop :=
  ∃ hk : MemLp k 2 (Measure.prod ν ν), kernelIntegralOperator (hk.toLp k) = T

theorem RepresentsL2Kernel.ae_eq {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [SFinite ν] [MeasureTheory.IsSeparable ν]
    {T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν} {k j : X × X → ℂ}
    (hk : RepresentsL2Kernel ν T k) (hj : RepresentsL2Kernel ν T j) :
    k =ᵐ[ν.prod ν] j := by
  obtain ⟨hk, he⟩ := hk
  obtain ⟨hj, hf⟩ := hj
  obtain ⟨S, hS, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (ν := ν)
  letI : Countable S := hS.to_subtype
  have heq := kernelIntegralOperator_injective b (he.trans hf.symm)
  exact hk.coeFn_toLp.symm.trans (heq ▸ hj.coeFn_toLp)

section Weighted

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (w : G → ℝ)

local notation "ν" => μ.withDensity (fun x => ENNReal.ofReal (w x))

omit [T2Space G] in
/-- Positive continuous density preserves the null sets of the product
measure used for the kernels. -/
theorem weightedKernel_ae_eq_iff (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (k j : G × G → ℂ) :
    k =ᵐ[Measure.prod ν ν] j ↔ k =ᵐ[μ.prod μ] j := by
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hp x)).ne')
  exact ⟨fun h => h.filter_mono (hμν.prod hμν).ae_le,
    fun h => h.filter_mono (hνμ.prod hνμ).ae_le⟩

private theorem weightedConvolutionRow_integrable (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (φ : C_c(G, ℂ)) (f : Lp ℂ 2 ν) (x : G) :
    Integrable (fun y => φ (x * y⁻¹) * f y) μ := by
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let e := (Homeomorph.inv G).trans (Homeomorph.mulLeft x)
  have hrow : Continuous (fun y => φ (x * y⁻¹)) :=
    φ.continuous.comp e.continuous
  have hrowc : HasCompactSupport (fun y => φ (x * y⁻¹)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (e.isProperMap.isCompact_preimage φ.hasCompactSupport)
    exact fun y hy => subset_tsupport _ hy
  let b (y : G) := φ (x * y⁻¹) / (w y : ℂ)
  have hbc : Continuous b := hrow.div (Complex.continuous_ofReal.comp hw)
    (fun y => Complex.ofReal_ne_zero.mpr (hp y).ne')
  have hb : MemLp b 2 ν :=
    hbc.memLp_of_hasCompactSupport (by
      unfold b
      simp_rw [div_eq_mul_inv]
      exact hrowc.mul_right (f' := fun y => (w y : ℂ)⁻¹))
  have hprod : MemLp (b * (f : G → ℂ)) 1 ν :=
    (Lp.memLp f).mul' hb
  have hi : Integrable (fun y => b y * f y) ν := memLp_one_iff_integrable.mp hprod
  have h := (integrable_withDensity_iff_integrable_smul' hw.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  refine h.congr (Eventually.of_forall fun y => ?_)
  change (ENNReal.ofReal (w y)).toReal • (b y * f y) = φ (x * y⁻¹) * f y
  rw [ENNReal.toReal_ofReal (hp y).le, Complex.real_smul, ← mul_assoc]
  congr 1
  unfold b
  rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hp y).ne')]

/-- Given the spectral part of convolution, form its Haar kernel and the
geometric remainder, with exactly one reciprocal density in the integration
variable when using the weighted measure. -/
theorem weightedSpectralKernel_decomposition (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (φ : C_c(G, ℂ)) (A B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hA : ∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂μ,
      A f x = ∫ y, φ y * f (y⁻¹ * x) ∂μ)
    (hB : B ∈ nuclearOperators (Lp ℂ 2 ν))
    (ρ : G → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let M := cutoffOperator (μ := ν) ρ hρ hρ₀ hρ₁
    ∃ k : G × G → ℂ,
      RepresentsL2Kernel ν B (fun z => k z / (w z.2 : ℂ)) ∧
      RepresentsL2Kernel ν (M.comp B) (fun z => (ρ z.1 : ℂ) * k z / (w z.2 : ℂ)) ∧
      RepresentsL2Kernel ν (M.comp (A - B))
        (fun z => (ρ z.1 : ℂ) * (φ (z.1 * z.2⁻¹) - k z) / (w z.2 : ℂ)) ∧
      ∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂μ,
        (A - B) f x = ∫ y, (φ (x * y⁻¹) - k (x, y)) * f y ∂μ := by
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  intro M
  have hρℂ := Complex.continuous_ofReal.measurable.comp hρ
  have hρcℂ : HasCompactSupport (fun x => (ρ x : ℂ)) := hρc.comp_left Complex.ofReal_zero
  have hbound (x : G) : ‖(ρ x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hρ₀ x)]
    exact hρ₁ x
  let J := cutoffConvolutionKernel w (fun x => (ρ x : ℂ)) φ
  have hJ : MemLp J 2 (Measure.prod ν ν) :=
    cutoffConvolutionKernel_memLp_of_measurable_cutoff μ hw hp hρℂ
      φ.continuous.measurable.aemeasurable ⟨1, hbound⟩
      (φ.hasCompactSupport.exists_bound_of_continuous φ.continuous) hρcℂ φ.hasCompactSupport
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hp x)).ne')
  have hJop : kernelIntegralOperator (hJ.toLp J) = M.comp A := by
    ext f : 1
    apply Lp.ext
    filter_upwards [hνμ.ae_le (cutoffConvolutionKernel_apply_of_measurable_cutoff μ hw hp hρℂ
      φ.continuous.measurable.aemeasurable ⟨1, hbound⟩
      (φ.hasCompactSupport.exists_bound_of_continuous φ.continuous) hρcℂ φ.hasCompactSupport f),
      hνμ.ae_le (hA f), cutoffOperator_ae ρ hρ hρ₀ hρ₁ (A f)] with x hx ha hm
    change kernelIntegralOperator (hJ.toLp J) f x = M (A f) x
    rw [hm, ha]
    exact hx
  obtain ⟨R, hR⟩ := hB
  obtain ⟨K, hK, _⟩ := R.exists_hilbertSchmidtKernel ν
  let k (z : G × G) := (w z.2 : ℂ) * K z
  have hk (z : G × G) : k z / (w z.2 : ℂ) = K z := by
    change (w z.2 : ℂ) * K z / (w z.2 : ℂ) = K z
    rw [mul_comm, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (hp z.2).ne')]
  have hcutEq : lpTwoComplexMultiplier (μ := ν) hρℂ.aestronglyMeasurable
      (Eventually.of_forall hbound) = M := by
    ext f : 1
    apply Lp.ext
    exact (lpTwoComplexMultiplier_ae hρℂ.aestronglyMeasurable
      (Eventually.of_forall hbound) f).trans (cutoffOperator_ae ρ hρ hρ₀ hρ₁ f).symm
  let Kρ (z : G × G) := (ρ z.1 : ℂ) * K z
  obtain ⟨hKρ, hKρop⟩ := kernelIntegralOperator_mul_left hρℂ.aestronglyMeasurable
    (Eventually.of_forall hbound) (Lp.memLp K)
  have hKρop' : kernelIntegralOperator (hKρ.toLp Kρ) = M.comp B := by
    have he : kernelIntegralOperator (hKρ.toLp Kρ) =
        (lpTwoComplexMultiplier hρℂ.aestronglyMeasurable (Eventually.of_forall hbound)).comp
          (kernelIntegralOperator ((Lp.memLp K).toLp (K : G × G → ℂ))) := hKρop
    rw [he, hcutEq, Lp.toLp_coeFn, hK, hR]
  have hgeom (z : G × G) : (ρ z.1 : ℂ) * (φ (z.1 * z.2⁻¹) - k z) / (w z.2 : ℂ) =
      J z - Kρ z := by
    unfold J Kρ cutoffConvolutionKernel
    simp only [mul_sub, sub_div, mul_div_assoc, hk]
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · simp only [hk]
    exact ⟨Lp.memLp K, by rw [Lp.toLp_coeFn, hK, hR]⟩
  · simp only [mul_div_assoc, hk]
    exact ⟨hKρ, hKρop'⟩
  · simp only [hgeom]
    refine ⟨hJ.sub hKρ, ?_⟩
    change kernelIntegralOperator ((hJ.sub hKρ).toLp (J - Kρ)) = _
    rw [MemLp.toLp_sub]
    change kernelIntegralOperatorCLM (hJ.toLp J - hKρ.toLp Kρ) = _
    rw [map_sub]
    change kernelIntegralOperator (hJ.toLp J) - kernelIntegralOperator (hKρ.toLp Kρ) = _
    rw [hJop, hKρop', ContinuousLinearMap.comp_sub]
  · intro f
    filter_upwards [hA f, kernelIntegralOperator_haarDensity_apply μ w hw hp (Lp.memLp K) f,
      hμν.ae_le (Lp.coeFn_sub (A f) (B f))] with x hx hy hz
    rw [sub_apply, hz, Pi.sub_apply, hx]
    rw [Lp.toLp_coeFn, hK, hR] at hy
    have hsubst : (∫ y, φ y * f (y⁻¹ * x) ∂μ) = ∫ y, φ (x * y⁻¹) * f y ∂μ := by
      let g y := φ (x * y⁻¹) * f y
      have hchange : (∫ y, g (y⁻¹ * x) ∂μ) = ∫ y, g y ∂μ := by
        rw [integral_inv_eq_self (fun y => g (y * x)) μ, integral_mul_right_eq_self g x]
      simpa only [g, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using hchange
    rw [hsubst, hy.2]
    have hφ := weightedConvolutionRow_integrable μ w hw hp φ f x
    rw [← integral_sub hφ hy.1]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      change φ (x * y⁻¹) * f y - k (x, y) * f y = (φ (x * y⁻¹) - k (x, y)) * f y
      rw [sub_mul])

end Weighted

section Global

variable (F : Type*) [Field F] [NumberField F]

local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]

local instance weightedLocallyFinite (l r s : ℝ) :
    IsLocallyFiniteMeasure (globalHardySobolevMeasure F μ l r s) := by
  rw [globalHardySobolevMeasure_eq_withDensity]
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_hardySobolevWeight l r s).comp
      (continuous_toAdd.comp (ideleClassLogNorm_continuous F)))

omit [μ.IsHaarMeasure] in
/-- An operator in amplitude coordinates transported to the actual weighted
Hardy–Sobolev space. -/
def globalHardySobolevUnchart (l r s : ℝ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 (globalHardySobolevMeasure F μ l r s) →L[ℂ]
      Lp ℂ 2 (globalHardySobolevMeasure F μ l r s) :=
  let e := globalHardySobolevIso F μ l r s
  e.symm.toLinearIsometry.toContinuousLinearMap.comp (T.comp e.toLinearIsometry.toContinuousLinearMap)

/-- Exhausting the logarithmic norm bands removes the compact cutoff from
the pointwise Haar convolution formula. -/
theorem globalHardySobolevConvolution_haar_ae (l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) (v : Lp ℂ 2 (globalHardySobolevMeasure F μ l r s)) :
    ∀ᵐ x ∂μ, globalHardySobolevUnchart F μ l r s
      (globalHardySobolevConvolution F μ l r s hs φ) v x =
      ∫ g, φ g * v (g⁻¹ * x) ∂μ := by
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  let K (n : ℕ) : Set (IdeleClass F) := {x | (m x).toAdd ∈ Icc (-(n : ℝ)) n}
  let ρ (n : ℕ) := (K n).indicator (fun _ => (1 : ℝ))
  have hc (n : ℕ) : IsCompact (K n) := ideleClass_logNormBand_compact F _ _
  have hρ (n : ℕ) : Measurable (ρ n) := measurable_const.indicator (hc n).isClosed.measurableSet
  have hρc (n : ℕ) : HasCompactSupport (ρ n) :=
    HasCompactSupport.of_support_subset_isCompact (hc n) support_indicator_subset
  have hρ₀ (n : ℕ) (x : IdeleClass F) : 0 ≤ ρ n x := by
    by_cases hx : x ∈ K n <;> simp [ρ, hx]
  have hρ₁ (n : ℕ) (x : IdeleClass F) : ρ n x ≤ 1 := by
    by_cases hx : x ∈ K n <;> simp [ρ, hx]
  let a (x : IdeleClass F) := hardySobolevAmplitude l r s (m x).toAdd
  have ha : Measurable a := (Real.continuous_sqrt.comp
    ((continuous_hardySobolevWeight l r s).comp (continuous_toAdd.comp m.continuous))).measurable
  have hp (x : IdeleClass F) : 0 < a x := by
    unfold a hardySobolevAmplitude hardySobolevWeight
    exact Real.sqrt_pos.2 (mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
      (Real.rpow_pos_of_pos (by positivity) _))
  let e := globalHardySobolevIso F μ l r s
  let u := globalHardySobolevUnchart F μ l r s (globalHardySobolevConvolution F μ l r s hs φ) v
  have hchart : ((e u) : IdeleClass F → ℂ) =ᵐ[μ] fun x => (a x : ℂ) * u x := by
    change ((amplitudeL2Iso μ a ha hp u) : IdeleClass F → ℂ) =ᵐ[μ] fun x => (a x : ℂ) * u x
    filter_upwards [amplitudeL2Iso_ae μ a ha hp u] with x hx
    exact hx.trans Complex.real_smul
  have hu : e u = globalHardySobolevConvolution F μ l r s hs φ (e v) := by
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  have hchartFormula (n : ℕ) : ∀ᵐ x ∂μ, ρ n x = 1 →
      e u x = (a x : ℂ) * ∫ g, φ g * v (g⁻¹ * x) ∂μ := by
    rw [hu]
    have h := hardySobolevConvolution_ae_on_cutoff μ m l r s hs φ (ρ n) (hρ n) (hρc n)
      (hρ₀ n) (hρ₁ n)
    exact h v
  filter_upwards [hchart, ae_all_iff.mpr hchartFormula] with x hx hf
  obtain ⟨n, hn⟩ := exists_nat_ge |(m x).toAdd|
  have hxK : x ∈ K n := abs_le.mp hn
  have hxρ : ρ n x = 1 := indicator_of_mem hxK _
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hp x).ne') (hx.symm.trans (hf n hxρ))

/-- The source-variable density, the two cutoff kernels and the geometric
Haar action on the actual closed theta subspace. -/
def GlobalProjectedKernelFormulas (l r s : ℝ) (φ : C_c(IdeleClass F, ℂ))
    (ρ : IdeleClass F → ℝ) (hρ : Measurable ρ) (h₀ : ∀ x, 0 ≤ ρ x) (h₁ : ∀ x, ρ x ≤ 1)
    (N : Submodule ℂ (Lp ℂ 2 μ)) (A B G : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  let w (x : IdeleClass F) := hardySobolevWeight l r s (ideleClassLogNorm F x).toAdd
  let ν := globalHardySobolevMeasure F μ l r s
  letI : IsLocallyFiniteMeasure ν := weightedLocallyFinite F μ l r s
  let M := cutoffOperator (μ := ν) ρ hρ h₀ h₁
  let B' := globalHardySobolevUnchart F μ l r s B
  let G' := globalHardySobolevUnchart F μ l r s G
  let A' := globalHardySobolevUnchart F μ l r s A
  ∃ k : IdeleClass F × IdeleClass F → ℂ,
    RepresentsL2Kernel ν B' (fun z => k z / (w z.2 : ℂ)) ∧
    RepresentsL2Kernel ν (M.comp B') (fun z => (ρ z.1 : ℂ) * k z / (w z.2 : ℂ)) ∧
    RepresentsL2Kernel ν (M.comp G')
      (fun z => (ρ z.1 : ℂ) * (φ (z.1 * z.2⁻¹) - k z) / (w z.2 : ℂ)) ∧
    ∀ f : Lp ℂ 2 ν, globalHardySobolevIso F μ l r s f ∈ N →
      A' f = G' f ∧ ∀ᵐ x ∂μ, G' f x = ∫ y, (φ (x * y⁻¹) - k (x, y)) * f y ∂μ

private theorem globalProjectedKernelFormulas_of_nuclear
    (l r s : ℝ) (hs : 0 ≤ s) (φ : C_c(IdeleClass F, ℂ))
    (ρ : IdeleClass F → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (h₀ : ∀ x, 0 ≤ ρ x) (h₁ : ∀ x, ρ x ≤ 1)
    (N : Submodule ℂ (Lp ℂ 2 μ)) (B G : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hB : B ∈ nuclearOperators (Lp ℂ 2 μ))
    (hBN : ∀ x ∈ N, B x = 0)
    (hG : globalHardySobolevConvolution F μ l r s hs φ - B = G) :
    GlobalProjectedKernelFormulas F μ l r s φ ρ hρ h₀ h₁ N
      (globalHardySobolevConvolution F μ l r s hs φ) B G := by
  let e := globalHardySobolevIso F μ l r s
  let A := globalHardySobolevConvolution F μ l r s hs φ
  let A' := globalHardySobolevUnchart F μ l r s A
  let B' := globalHardySobolevUnchart F μ l r s B
  let G' := globalHardySobolevUnchart F μ l r s G
  let ν := globalHardySobolevMeasure F μ l r s
  let w (x : IdeleClass F) := hardySobolevWeight l r s (ideleClassLogNorm F x).toAdd
  have hw : Continuous w := (continuous_hardySobolevWeight l r s).comp
    (continuous_toAdd.comp (ideleClassLogNorm_continuous F))
  have hp (x : IdeleClass F) : 0 < w x := by
    unfold w hardySobolevWeight
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos (by positivity) _)
  letI : IsLocallyFiniteMeasure ν := weightedLocallyFinite F μ l r s
  have hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x)) :=
    globalHardySobolevMeasure_eq_withDensity F μ l r s
  let T : TraceClass (Lp ℂ 2 μ) := (⟨B, hB⟩ : ↥(nuclearOperators (Lp ℂ 2 μ)))
  have htransport := traceClass_transport e.symm.toLinearIsometry.toContinuousLinearMap
    e.toLinearIsometry.toContinuousLinearMap e.apply_symm_apply T
  obtain ⟨U, hU, _⟩ := htransport
  have hn : B' ∈ nuclearOperators (Lp ℂ 2 ν) := by
    change U.toOperator = B' at hU
    exact hU ▸ U.toOperator_mem
  have hGa : A' - B' = G' := by
    change globalHardySobolevUnchart F μ l r s A -
      globalHardySobolevUnchart F μ l r s B = globalHardySobolevUnchart F μ l r s G
    rw [← hG]
    unfold globalHardySobolevUnchart
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    rfl
  have hm (f : Lp ℂ 2 ν) (hf : e f ∈ N) : A' f = G' f := by
    rw [← hGa, sub_apply]
    have hz : B' f = 0 := by
      change e.symm (B (e f)) = 0
      rw [hBN _ hf, map_zero]
    rw [hz, sub_zero]
  have ha : ∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂μ, A' f x = ∫ g, φ g * f (g⁻¹ * x) ∂μ :=
    globalHardySobolevConvolution_haar_ae F μ l r s hs φ
  have hhelper (τ : Measure (IdeleClass F))
      (hτ : τ = μ.withDensity (fun x => ENNReal.ofReal (w x))) [SFinite τ] :
      ∀ A B : Lp ℂ 2 τ →L[ℂ] Lp ℂ 2 τ,
      (∀ f : Lp ℂ 2 τ, ∀ᵐ x ∂μ, A f x = ∫ g, φ g * f (g⁻¹ * x) ∂μ) →
      B ∈ nuclearOperators (Lp ℂ 2 τ) →
      ∃ k : IdeleClass F × IdeleClass F → ℂ,
        RepresentsL2Kernel τ B (fun z => k z / (w z.2 : ℂ)) ∧
        RepresentsL2Kernel τ ((cutoffOperator ρ hρ h₀ h₁).comp B)
          (fun z => (ρ z.1 : ℂ) * k z / (w z.2 : ℂ)) ∧
        RepresentsL2Kernel τ ((cutoffOperator ρ hρ h₀ h₁).comp (A - B))
          (fun z => (ρ z.1 : ℂ) * (φ (z.1 * z.2⁻¹) - k z) / (w z.2 : ℂ)) ∧
        ∀ f : Lp ℂ 2 τ, ∀ᵐ x ∂μ,
          (A - B) f x = ∫ y, (φ (x * y⁻¹) - k (x, y)) * f y ∂μ := by
    subst τ
    exact fun A B ha hb => weightedSpectralKernel_decomposition μ w hw hp φ A B ha hb
      ρ hρ hρc h₀ h₁
  obtain ⟨k, hk₁, hk₂, hk₃, hka⟩ := hhelper ν hν A' B' ha hn
  rw [hGa] at hk₃ hka
  exact ⟨k, hk₁, hk₂, hk₃, fun f hf => ⟨hm f hf, hka f⟩⟩

local instance globalKernelThetaClosed (a l r s : ℝ) (hs : 0 ≤ s) :
    IsClosed (globalThetaSobolevCompletion F μ a l r s hs : Set (Lp ℂ 2 μ)) :=
  globalThetaSobolevCompletion_isClosed F μ a l r s hs

/-- Corrected Theorem 10.4.3.4 on the central Sobolev line, with spectral
projection after convolution. Quotient nuclearity is the analytic input. -/
theorem globalLine_projectedKernelFormulas (a s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) (ρ : IdeleClass F → ℝ)
    (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (h₀ : ∀ x, 0 ≤ ρ x) (h₁ : ∀ x, ρ x ≤ 1) :
    let N := globalThetaSobolevCompletion F μ a 0 0 s hs
    let A := globalHardySobolevConvolution F μ 0 0 s hs φ
    ∀ Q : TraceClass (Lp ℂ 2 μ ⧸ N),
      Q.toOperator = globalSpectralConvolution F μ a 0 0 s hs φ →
      GlobalProjectedKernelFormulas F μ 0 0 s φ ρ hρ h₀ h₁ N A
        (Nᗮ.starProjection.comp A) (N.starProjection.comp A) := by
  intro N A Q hQ
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := globalKernelThetaClosed F μ a 0 0 s hs
  obtain ⟨T, hT, _⟩ := globalSpectralProjection_convolution_trace F μ a 0 0 s hs φ Q hQ
  refine globalProjectedKernelFormulas_of_nuclear F μ 0 0 s hs φ ρ hρ hρc h₀ h₁
    N _ _ (hT ▸ T.toOperator_mem) ?_ ?_
  · intro x hx
    have hAx : A x ∈ N := globalHardySobolevConvolution_preserves_theta F μ a 0 0 s hs φ hx
    exact Submodule.starProjection_orthogonal_apply_eq_zero hAx
  · ext x : 1
    change A x - Nᗮ.starProjection (A x) = N.starProjection (A x)
    exact sub_eq_iff_eq_add.mpr (N.starProjection_add_starProjection_orthogonal (A x)).symm

/-- Corrected Theorem 10.4.3.6 on compact strips, with convolution after
projection. The cutoff spectral kernel represents the cutoff spectral
operator. The uncut spectral operator is assumed trace class. -/
theorem globalStrip_projectedKernelFormulas (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) (ρ : IdeleClass F → ℝ)
    (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (h₀ : ∀ x, 0 ≤ ρ x) (h₁ : ∀ x, ρ x ≤ 1) :
    let N := globalThetaSobolevCompletion F μ a l r s hs
    let A := globalHardySobolevConvolution F μ l r s hs φ
    A.comp Nᗮ.starProjection ∈ nuclearOperators (Lp ℂ 2 μ) →
      GlobalProjectedKernelFormulas F μ l r s φ ρ hρ h₀ h₁ N A
        (A.comp Nᗮ.starProjection) (A.comp N.starProjection) := by
  intro N A hB
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := globalKernelThetaClosed F μ a l r s hs
  refine globalProjectedKernelFormulas_of_nuclear F μ l r s hs φ ρ hρ hρc h₀ h₁
    N _ _ hB ?_ ?_
  · intro x hx
    change A (Nᗮ.starProjection x) = 0
    rw [Submodule.starProjection_orthogonal_apply_eq_zero hx, map_zero]
  · ext x : 1
    change A x - A (Nᗮ.starProjection x) = A (N.starProjection x)
    have h := congrArg A (N.starProjection_add_starProjection_orthogonal x)
    rw [map_add] at h
    exact sub_eq_iff_eq_add.mpr h.symm


end Global

end

end Masullo
