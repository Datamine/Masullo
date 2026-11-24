import ModulatedSobolevCoefficients
import HardySobolevSequence

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]
variable (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)

local notation "RadialLp" => StripSobolev a b s
local notation "ScalarCutoff" => supportedSobolevCompletion a b s U
local notation "ProductCutoff" => lpTwoRadialSupport μ (stripMeasure a b s) U
local notation "KernelLp" => Lp ℂ 2 μ
local notation "ProductLp" => Lp ℂ 2 (μ.prod (stripMeasure a b s))

include hU

omit [SFinite μ] in
/-- The radial support subspace is the range of the product indicator projection. -/
theorem modulatedInterval_radialProjection :
    ∃ P : ProductLp →L[ℂ] ProductLp,
      IsClosed (ProductCutoff : Set ProductLp) ∧
      (∀ f, P f ∈ ProductCutoff) ∧ (∀ f : ProductCutoff, P f.val = f.val) ∧
      ∀ f, (P f : K × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure a b s)]
        (Prod.snd ⁻¹' U).indicator (f : K × ℝ → ℂ) := by
  obtain ⟨P, hclosed, _, hP⟩ := lpTwo_measurableCutoff
    (μ := μ.prod (stripMeasure a b s)) ((measurable_snd : Measurable (Prod.snd : K × ℝ → ℝ)) hU.measurableSet)
  have hmem (f : ProductLp) : P f ∈ ProductCutoff := by
    change ∀ᵐ p ∂μ.prod (stripMeasure a b s), p.2 ∉ U → P f p = 0
    filter_upwards [(hP f).2] with p hp hn
    exact hp.trans (indicator_of_notMem (show p ∉ Prod.snd ⁻¹' U from hn) _)
  have hfix (f : ProductCutoff) : P f.val = f.val := by
    apply Lp.ext
    filter_upwards [(hP f.val).2, f.property] with p hp hf
    by_cases h : p.2 ∈ U
    · exact hp.trans (indicator_of_mem (show p ∈ Prod.snd ⁻¹' U from h) _)
    · exact hp.trans ((indicator_of_notMem (show p ∉ Prod.snd ⁻¹' U from h) _).trans (hf h).symm)
  have hr : range P = (ProductCutoff : Set ProductLp) :=
    Set.ext fun f => ⟨fun ⟨w, hw⟩ => hw ▸ hmem w, fun h => ⟨f, hfix ⟨f, h⟩⟩⟩
  exact ⟨P, hr ▸ hclosed, hmem, hfix, fun f => (hP f).2⟩

/-- The algebraic Hilbert tensor embeds by pointwise products. -/
def modulatedIntervalTensorEmbedding :
    (KernelLp ⊗[ℂ] ScalarCutoff) →ₗᵢ[ℂ] ProductCutoff := by
  let J := lpTwoTensorIsometry.comp
    (TensorProduct.mapIsometry (LinearIsometry.id : KernelLp →ₗᵢ[ℂ] KernelLp)
      (Submodule.subtypeₗᵢ ScalarCutoff))
  have hmem (x : KernelLp ⊗[ℂ] ScalarCutoff) : J x ∈ ProductCutoff := by
    induction x using TensorProduct.induction_on with
    | zero => rw [J.map_zero]; exact Submodule.zero_mem ProductCutoff
    | add x y hx hy => simpa only [map_add] using (Submodule.add_mem ProductCutoff hx hy)
    | tmul u v =>
      change lpTwoProduct u v.val ∈ ProductCutoff
      have hv := (mem_supportedSobolevCompletion_iff a b s hU v.val).mp v.property
      have hac := amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
        (stripSobolevAmplitude a b s)
      have hν := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := stripMeasure a b s)
      change ∀ᵐ p ∂μ.prod (stripMeasure a b s), p.2 ∉ U → lpTwoProduct u v.val p = 0
      filter_upwards [lpTwoProduct_ae u v.val, hν.ae (hac.ae_le hv)] with p hp hzero hn
      exact hp.trans (by rw [hzero hn, mul_zero])
  exact ⟨J.toLinearMap.codRestrict _ hmem, J.norm_map⟩

theorem modulatedIntervalTensorEmbedding_tmul (u : KernelLp) (v : ScalarCutoff) :
    (modulatedIntervalTensorEmbedding μ a b s hU (u ⊗ₜ[ℂ] v)).val = lpTwoProduct u v.val := rfl

theorem denseRange_modulatedIntervalTensorEmbedding :
    DenseRange (modulatedIntervalTensorEmbedding μ a b s hU) := by
  obtain ⟨P, _, hmem, hfix, hP⟩ := modulatedInterval_radialProjection μ a b s hU
  obtain ⟨Q, _, _, _, hQrange, hQ⟩ := supportedSobolevCompletion_eq_cutoff a b s hU
  let P' := P.codRestrict ProductCutoff hmem
  let Q' := Q.codRestrict ScalarCutoff (fun v => by
    change Q v ∈ (ScalarCutoff : Set RadialLp)
    rw [← hQrange]
    exact mem_range_self v)
  have hPsurj : Surjective P' := fun u => ⟨u.val, Subtype.ext (hfix u)⟩
  let J := lpTwoTensorIsometry (μ := μ) (ν := stripMeasure a b s)
  let T := TensorProduct.map (LinearMap.id : KernelLp →ₗ[ℂ] KernelLp) Q'.toLinearMap
  have hcomm (x : KernelLp ⊗[ℂ] RadialLp) :
      P' (J x) = modulatedIntervalTensorEmbedding μ a b s hU (T x) := by
    induction x using TensorProduct.induction_on with
    | zero => rw [J.map_zero, P'.map_zero, T.map_zero, (modulatedIntervalTensorEmbedding μ a b s hU).map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u v =>
      apply Subtype.ext
      change P (lpTwoProduct u v) = lpTwoProduct u (Q v)
      apply Lp.ext
      have hac := amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
        (stripSobolevAmplitude a b s)
      have hν := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := stripMeasure a b s)
      filter_upwards [hP (lpTwoProduct u v), lpTwoProduct_ae u v,
        lpTwoProduct_ae u (Q v), hν.ae_eq_comp (hac.ae_le (hQ v))]
        with p hp huv hQv hq
      change Q v p.2 = U.indicator (v : ℝ → ℂ) p.2 at hq
      rw [hp, hQv, hq]
      by_cases h : p.2 ∈ U
      · rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' U from h), indicator_of_mem h, huv]
      · rw [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' U from h), indicator_of_notMem h, mul_zero]
  refine hPsurj.denseRange.dense_of_mapsTo P'.continuous denseRange_lpTwoTensorIsometry ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨T x, (hcomm x).symm⟩

omit [SFinite μ] in
private theorem modulatedInterval_radialSupport_complete : CompleteSpace ProductCutoff := by
  obtain ⟨_, hc, _, _, _⟩ := modulatedInterval_radialProjection μ a b s hU
  exact hc.completeSpace_coe

/-- The Hilbert tensor of the compact factor with the supported scalar completion
is precisely the corresponding supported product space. -/
def modulatedIntervalTensorEquiv :
    Completion (KernelLp ⊗[ℂ] ScalarCutoff) ≃ₗᵢ[ℂ] ProductCutoff :=
  letI : CompleteSpace ProductCutoff := modulatedInterval_radialSupport_complete μ a b s hU
  completionLinearIsometryEquiv (modulatedIntervalTensorEmbedding μ a b s hU)
    (denseRange_modulatedIntervalTensorEmbedding μ a b s hU)

theorem modulatedIntervalTensorEquiv_tmul (u : KernelLp) (v : ScalarCutoff) :
    (modulatedIntervalTensorEquiv μ a b s hU
      ((u ⊗ₜ[ℂ] v : KernelLp ⊗[ℂ] ScalarCutoff) : Completion (KernelLp ⊗[ℂ] ScalarCutoff))).val =
      lpTwoProduct u v.val := by
  letI : CompleteSpace ProductCutoff := modulatedInterval_radialSupport_complete μ a b s hU
  exact (congrArg Subtype.val (completionLinearIsometryEquiv_coe _ _ (u ⊗ₜ[ℂ] v))).trans
    (modulatedIntervalTensorEmbedding_tmul μ a b s hU u v)


omit [SFinite μ] in
/-- The radial support projection for a singleton Sobolev base. -/
theorem modulatedSobolev_radialProjection :
    ∃ P : Lp ℂ 2 (μ.prod (stripMeasure b b s)) →L[ℂ] Lp ℂ 2 (μ.prod (stripMeasure b b s)),
      IsClosed (lpTwoRadialSupport μ (stripMeasure b b s) U : Set (Lp ℂ 2 (μ.prod (stripMeasure b b s)))) ∧
      (∀ f, P f ∈ lpTwoRadialSupport μ (stripMeasure b b s) U) ∧
      (∀ f : lpTwoRadialSupport μ (stripMeasure b b s) U, P f.val = f.val) ∧
      ∀ f, (P f : K × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure b b s)]
        (Prod.snd ⁻¹' U).indicator (f : K × ℝ → ℂ) :=
  modulatedInterval_radialProjection μ b b s hU

abbrev modulatedSupportedTensorEmbedding :=
  modulatedIntervalTensorEmbedding μ b b s hU

theorem modulatedSupportedTensorEmbedding_tmul (u : KernelLp)
    (v : supportedSobolevCompletion b b s U) :
    (modulatedSupportedTensorEmbedding μ b s hU (u ⊗ₜ[ℂ] v)).val = lpTwoProduct u v.val :=
  modulatedIntervalTensorEmbedding_tmul μ b b s hU u v

theorem denseRange_modulatedSupportedTensorEmbedding :
    DenseRange (modulatedSupportedTensorEmbedding μ b s hU) :=
  denseRange_modulatedIntervalTensorEmbedding μ b b s hU

abbrev modulatedSupportedTensorEquiv :=
  modulatedIntervalTensorEquiv μ b b s hU

theorem modulatedSupportedTensorEquiv_tmul (u : KernelLp) (v : supportedSobolevCompletion b b s U) :
    (modulatedSupportedTensorEquiv μ b s hU
      ((u ⊗ₜ[ℂ] v : KernelLp ⊗[ℂ] supportedSobolevCompletion b b s U) :
        Completion (KernelLp ⊗[ℂ] supportedSobolevCompletion b b s U))).val =
      lpTwoProduct u v.val :=
  modulatedIntervalTensorEquiv_tmul μ b b s hU u v

end

end Masullo
