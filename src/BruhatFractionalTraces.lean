import BruhatHalfLineCompletion
import FractionalMellinBoundary
import CompactCharacterCompleteness

open Filter Function MeasureTheory Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

local notation "K" => m.toMonoidHom.ker
local notation "E[" I "]" => ModulatedExponentialInductive m I
local notation "dx" => (volume : Measure ℝ)

/-- On a line belonging to the source decay set, every genuine Bruhat test
has the fractional trace of its original group Mellin integral. -/
theorem bruhatFractionalLine_values_ae {I : Set ℝ} (t : I) {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual K) (f : E[I]) :
    (fractionalMellinTensorValues ν hs χ (fractionalMellinTensor ν t s
      (bruhatIntervalEndpointInclusion m τ hτ ν t s f)) : ℝ → ℂ) =ᵐ[dx]
      fun y => bruhatGroupMellinMoment m τ hτ ν χ f.val 0
        (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) := by
  let e := intervalGroupChart m τ hτ
  let v := bruhatIntervalEndpointInclusion m τ hτ ν t s f
  let w := bruhatIntervalEndpointInclusion m τ hτ ν t 2 f
  let F (g : K × ℝ → ℂ) (z : ℂ) (p : K × ℝ) :=
    (χ p.1 : ℂ) * g p * mellinEvaluationKernel 0 z p.2
  let u : lpTwoRadialSupport ν (stripMeasure t t 2) univ :=
    ⟨w, by change ∀ᵐ p ∂ν.prod (stripMeasure t t 2), p.2 ∉ univ → w p = 0; simp⟩
  have hae (r : ℝ) :
      (bruhatIntervalEndpointInclusion m τ hτ ν t r f : K × ℝ → ℂ)
        =ᵐ[ν.prod dx] f.val ∘ e :=
    (Measure.AbsolutelyContinuous.rfl.prod
      (absolutelyContinuous_amplitudeMeasure dx _
        (stripSobolevAmplitude_continuous t t r).measurable (stripSobolevAmplitude_pos t t r))).ae_le
          (bruhatIntervalEndpointInclusion_ae m τ hτ ν t r f)
  have hfi {g h : K × ℝ → ℂ} (hg : g =ᵐ[ν.prod dx] h) (z : ℂ) :
      F g z =ᵐ[ν.prod dx] F h z := hg.mono fun p hp =>
    congrArg (fun q : ℂ => (χ p.1 : ℂ) * q * mellinEvaluationKernel 0 z p.2) hp
  have hi (y : ℝ) : Integrable (F v (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ)) (ν.prod dx) := by
    let z : ℂ := ⟨(t : ℝ), 2 * Real.pi * y⟩
    have hk : MemLp ((univ : Set ℝ).indicator (mellinEvaluationKernel 0 z)) 2
        (stripMeasure (-(t : ℝ)) (-(t : ℝ)) (-2)) := by
      rw [indicator_univ]
      apply (mellinEvaluationKernel_memLp_iff (z := z) (a := (t : ℝ)) (b := (t : ℝ))
        le_rfl le_rfl (by norm_num) 0).mpr
      exact Or.inr (by norm_num)
    obtain ⟨_, hL, _⟩ := modulatedInterval_mellinMoment_of_kernel ν t t 2 isOpen_univ χ 0 z hk
    exact (hL u).1.congr (hfi ((hae 2).trans (hae s).symm) z)
  refine (fractionalMellinTensor_values_ae ν t hs χ v hi).trans (.of_forall fun y => ?_)
  let z : ℂ := ⟨(t : ℝ), 2 * Real.pi * y⟩
  have he : MeasurePreserving e (ν.prod dx) (modulatedLogMeasure m τ hτ ν) :=
    intervalGroupChart_preserving m τ hτ ν dx
  change (∫ p, F v z p ∂ν.prod dx) = bruhatGroupMellinMoment m τ hτ ν χ f.val 0 z
  unfold bruhatGroupMellinMoment
  rw [← he.integral_comp e.toMeasurableEquiv.measurableEmbedding]
  refine (integral_congr_ae (hfi (hae s) z)).trans (integral_congr_ae (.of_forall fun p => ?_))
  change F (f.val ∘ e) z p = (bruhatGroupMellinIntegrand m τ hτ χ f.val 0 z) (e p)
  have hp := intervalGroupChart_log m τ hτ p
  change modulatedLog m (e p) = p.2 at hp
  simp only [F, Function.comp_apply, bruhatGroupMellinIntegrand, hp]
  change (χ p.1 : ℂ) * f.val (e p) * mellinEvaluationKernel 0 z p.2 =
    (χ (e.symm (e p)).1 : ℂ) * f.val (e p) * mellinEvaluationKernel 0 z p.2
  rw [e.symm_apply_apply]


/-- A fractional line restriction of a weighted Bruhat class is the
fractional transform of the same test evaluated at that line. -/
theorem bruhatFractionalIntervalTrace_onTest {I : Set ℝ} {a b t : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (ht : t ∈ Icc a b) (htI : t ∈ I)
    (s : ℝ) (f : E[I]) :
    fractionalIntervalTrace ν hab s ht (bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s f) =
      fractionalMellinTensor ν t s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨t, htI⟩ s f) := by
  let v := bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s f
  have hm : ν.prod (stripMeasure t t s) ≤ ν.prod (stripMeasure a b s) := by
    rw [modulatedInterval_prod_weightedMeasure ν (a := t) le_rfl,
      modulatedInterval_prod_weightedMeasure ν hab]
    apply withDensity_mono
    exact .of_forall fun p => ENNReal.ofReal_le_ofReal
      (hardySobolevWeight_mono_interval ht.1 ht.2 ht.1 ht.2 s p.2)
  change fractionalMellinTensor ν t s (lpTwoMeasureInclusion hm v) = _
  apply congrArg (fractionalMellinTensor ν t s)
  apply Lp.ext
  filter_upwards [lpTwoMeasureInclusion_ae hm v,
    hm.absolutelyContinuous.ae_le (bruhatCompactIntervalInclusion_ae m τ hτ ν ha hb hab s f),
    bruhatIntervalEndpointInclusion_ae m τ hτ ν (⟨t, htI⟩ : I) s f] with p hp hv hw
  exact hp.trans (hv.trans hw.symm)

private theorem bruhatFractionalProduct_dense [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) :
    DenseRange (bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s) := by
  let J := bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s
  let R := lpTwoRadialSupport ν (stripMeasure a b s) univ
  let T := bruhatCompactIntervalCutoffInclusion m τ hτ ν ha hb hab s univ
  have hT : DenseRange T := bruhatCompactIntervalCutoff_dense m τ hτ ν hm ha hb hab s isOpen_univ
  have hV : Surjective (Subtype.val : R → Lp ℂ 2 (ν.prod (stripMeasure a b s))) := by
    intro u
    refine ⟨⟨u, ?_⟩, rfl⟩
    change ∀ᵐ p ∂ν.prod (stripMeasure a b s), p.2 ∉ univ → u p = 0
    simp
  have h := hV.denseRange.comp hT continuous_subtype_val
  exact h.mono (by rintro _ ⟨f, rfl⟩; exact ⟨f.val, rfl⟩)

/-- Closed compatible fractional endpoint pairs are exactly the completion
of the two original Mellin line traces of Bruhat tests. -/
theorem bruhatFractionalInterval_endpoints_closure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) :
    let A := fractionalIntervalTrace ν hab s (left_mem_Icc.mpr hab)
    let B := fractionalIntervalTrace ν hab s (right_mem_Icc.mpr hab)
    closure (range (fun f : E[I] =>
      (fractionalMellinTensor ν a s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨a, ha⟩ s f),
       fractionalMellinTensor ν b s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f)))) =
      range (A.prod B) := by
  intro A B
  let J := A.prod B
  let T := bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s
  have hJ : IsClosedEmbedding J := (fractionalIntervalEndpoints_closedEmbedding ν hab s).1
  have hEq (f : E[I]) : J (T f) =
      (fractionalMellinTensor ν a s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨a, ha⟩ s f),
       fractionalMellinTensor ν b s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f)) :=
    Prod.ext (bruhatFractionalIntervalTrace_onTest m τ hτ ν ha hb hab (left_mem_Icc.mpr hab) ha s f)
      (bruhatFractionalIntervalTrace_onTest m τ hτ ν ha hb hab (right_mem_Icc.mpr hab) hb s f)
  change _ = range J
  simp_rw [← hEq]
  change closure (range (J ∘ T)) = range J
  rw [range_comp, hJ.closure_image_eq,
    (bruhatFractionalProduct_dense m τ hτ ν hm ha hb hab s).closure_range, image_univ]


private theorem bruhatFractionalSupportedEndpoint_closure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I R V : Set ℝ} (hV : IsOpen V) (hVR : V ⊆ R)
    {b : ℝ} (hb : b ∈ I) (s : ℝ)
    (he : ∀ᵐ p ∂ν.prod (stripMeasure b b s), p.2 ∈ V ↔ p.2 ∈ R) :
    closure (range (fun f : bruhatIntervalCutoffTests m I R =>
      fractionalMellinTensor ν b s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f.val))) =
    (fractionalMellinSupportedSpace ν s R : Set (FractionalMellinTensor ν s)) := by
  let A := Lp ℂ 2 (ν.prod (stripMeasure b b s))
  let J := bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s
  let F := fractionalMellinTensor ν b s
  let S := lpTwoRadialSupport ν (stripMeasure b b s) R
  let S' := lpTwoRadialSupport ν (stripMeasure b b s) V
  have hS : S' = S := by
    ext f
    change (∀ᵐ p ∂ν.prod (stripMeasure b b s), p.2 ∉ V → f p = 0) ↔
      (∀ᵐ p ∂ν.prod (stripMeasure b b s), p.2 ∉ R → f p = 0)
    exact eventually_congr (he.mono fun p hp => by simp only [hp])
  have hJ (f : bruhatIntervalCutoffTests m I R) : J f.val ∈ S := by
    change ∀ᵐ p ∂ν.prod (stripMeasure b b s), p.2 ∉ R → J f.val p = 0
    filter_upwards [bruhatIntervalEndpointInclusion_ae m τ hτ ν (⟨b, hb⟩ : I) s f.val]
      with p hp hn
    rw [hp]
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hf := f.property hs
    have hlog (q : K × ℝ) :
        modulatedLog m (τ (Multiplicative.ofAdd q.2) * q.1.val) = q.2 :=
      intervalGroupChart_log m τ hτ q
    exact hn ((hlog p) ▸ hf)
  have hclosed : IsClosed (S : Set A) := by
    obtain ⟨_, hc, _, _, _⟩ := modulatedInterval_radialProjection ν b b s hV
    exact hS ▸ hc
  let J' := bruhatCompactIntervalCutoffInclusion m τ hτ ν hb hb le_rfl s V
  have hJ' : DenseRange J' := bruhatCompactIntervalCutoff_dense m τ hτ ν hm hb hb le_rfl s hV
  have hincl : IsClosedEmbedding ((↑) : S' → A) := by
    apply IsClosed.isClosedEmbedding_subtypeVal
    exact hS.symm ▸ hclosed
  have hclosure : closure (range (Subtype.val ∘ J' : _ → A)) = (S : Set A) := by
    rw [range_comp, hincl.closure_image_eq, hJ'.closure_range, image_univ, Subtype.range_coe, hS]
  have hL (f : E[I]) : bruhatCompactIntervalInclusion m τ hτ ν hb hb le_rfl s f = J f := by
    exact Lp.ext ((bruhatCompactIntervalInclusion_ae m τ hτ ν hb hb le_rfl s f).trans
      (bruhatIntervalEndpointInclusion_ae m τ hτ ν (⟨b, hb⟩ : I) s f).symm)
  have hR : closure (range (fun f : bruhatIntervalCutoffTests m I R => J f.val)) = (S : Set A) := by
    apply le_antisymm
    · exact closure_minimal (by rintro _ ⟨f, rfl⟩; exact hJ f) hclosed
    · rw [← hclosure]
      apply closure_mono
      rintro _ ⟨f, rfl⟩
      refine ⟨⟨f.val, f.property.trans (preimage_mono hVR)⟩, ?_⟩
      exact (hL f.val).symm
  change closure (range (F ∘ fun f : bruhatIntervalCutoffTests m I R => J f.val)) = _
  rw [range_comp, F.isometry.isClosedEmbedding.closure_image_eq, hR]
  ext u
  obtain ⟨f, rfl⟩ := F.surjective u
  constructor
  · rintro ⟨v, hv, heq⟩
    exact (fractionalMellinSupportedSpace_mem_iff ν b s R f).mpr (F.injective heq ▸ hv)
  · intro h
    exact ⟨f, (fractionalMellinSupportedSpace_mem_iff ν b s R f).mp h, rfl⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [CompactSpace K] [IsFiniteMeasure ν] in
private theorem bruhatRadialEndpoint_ae_ne (b s c : ℝ) :
    ∀ᵐ p : K × ℝ ∂ν.prod (stripMeasure b b s), p.2 ≠ c :=
  (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := stripMeasure b b s)).ae
    ((amplitudeMeasure_absolutelyContinuous dx (stripSobolevAmplitude b b s)).ae_le ((dx).ae_ne c))

/-- The boundary trace completion of the original finite-norm right-half-line
tests is the analytic subspace with nonpositive inverse Fourier support. -/
theorem bruhatFractionalRightHalfLine_traceClosure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {b : ℝ} (hb : b ∈ I) (s : ℝ) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (Iic 0) =>
      fractionalMellinTensor ν b s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f.val))) =
    (fractionalMellinSupportedSpace ν s (Iic 0) : Set (FractionalMellinTensor ν s)) := by
  apply bruhatFractionalSupportedEndpoint_closure m τ hτ ν hm isOpen_Iio Iio_subset_Iic_self hb s
  filter_upwards [bruhatRadialEndpoint_ae_ne m ν b s 0] with p hp
  change p.2 < 0 ↔ p.2 ≤ 0
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hp⟩

/-- The boundary trace completion of the original finite-norm left-half-line
tests is the analytic subspace with nonnegative inverse Fourier support. -/
theorem bruhatFractionalLeftHalfLine_traceClosure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {b : ℝ} (hb : b ∈ I) (s : ℝ) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (Ici 0) =>
      fractionalMellinTensor ν b s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f.val))) =
    (fractionalMellinSupportedSpace ν s (Ici 0) : Set (FractionalMellinTensor ν s)) := by
  apply bruhatFractionalSupportedEndpoint_closure m τ hτ ν hm isOpen_Ioi Ioi_subset_Ici_self hb s
  filter_upwards [bruhatRadialEndpoint_ae_ne m ν b s 0] with p hp
  change 0 < p.2 ↔ 0 ≤ p.2
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hp.symm⟩


section AngularPlancherel

variable [ν.IsMulLeftInvariant] [ν.WeaklyRegular] [IsProbabilityMeasure ν]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- Pullback to split coordinates followed by angular Fourier transform.
The dual is realized as square-summable coefficients for counting measure. -/
theorem bruhatCompactInterval_angularTensor {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    ∃ U : Lp ℂ 2 ν ≃ₗᵢ[ℂ] lp (fun _ : PontryaginDual K => ℂ) 2,
      (∀ (f : Lp ℂ 2 ν) (χ : PontryaginDual K), U f χ = ∫ k, star (χ k : ℂ) * f k ∂ν) ∧
      Nonempty (Lp ℂ 2 (hardySobolevMeasure (modulatedLogMeasure m τ hτ ν) (modulatedLog m) a b s)
        ≃ₗᵢ[ℂ] UniformSpace.Completion ((lp (fun _ : PontryaginDual K => ℂ) 2) ⊗[ℂ] StripSobolev a b s)) := by
  obtain ⟨U, hU⟩ := exists_compactCharacterPlancherel ν
  exact ⟨U, hU, ⟨(bruhatCompactIntervalGroupProductEquiv m τ hτ ν hab s).trans
    (completedLpTwoTensorEquiv.symm.trans
      (completionCongrIsometry (TensorProduct.congrIsometry U (.refl ℂ _))))⟩⟩

end AngularPlancherel

end
end Masullo
