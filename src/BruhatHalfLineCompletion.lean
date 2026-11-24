import BruhatIntervalInclusion

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

local notation "E[" I "]" => ModulatedExponentialInductive m I
local notation "H" => modulatedLogMeasure m τ hτ ν
local notation "W[" b "," s "]" => hardySobolevMeasure H (modulatedLog m) b b s
local notation "N[" I "," s "]" => hardySobolevIntervalENorm H (modulatedLog m) I s

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace m.toMonoidHom.ker] in
theorem bruhatDecay_continuous_val {I : Set ℝ} (a : I) (f : E[I]) : Continuous f.val := by
  let g := modulatedDecayTwistCLM m I a f
  have hc : Continuous (fun x : G => Real.exp (-((a : ℝ) * (m x).toAdd))) :=
    Real.continuous_exp.comp ((continuous_const.mul (continuous_toAdd.comp m.continuous)).neg)
  apply (hc.smul (bruhatSchwartz_continuous g)).congr
  intro x
  change Real.exp (-((a : ℝ) * (m x).toAdd)) •
    modulatedExponentialWeight m a f.val x = f.val x
  rw [modulatedExponentialWeight_apply, smul_smul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_smul]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CompactSpace m.toMonoidHom.ker] in
private theorem splitHaar_openPos [ν.IsOpenPosMeasure] : (H).IsOpenPosMeasure :=
  (modulatedLogSplit m τ hτ).continuous.isOpenPosMeasure_map
    (modulatedLogSplit m τ hτ).surjective

private theorem bruhatEndpoint_eLpNorm {I : Set ℝ} {a : ℝ}
    (ha : a ∈ I) (s : ℝ) (f : E[I]) :
    eLpNorm f.val 2 W[a,s] = ‖bruhatCompactIntervalGroupInclusion m τ hτ ν ha ha le_rfl s f‖ₑ := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae (bruhatCompactIntervalGroupInclusion_ae m τ hτ ν ha ha le_rfl s f).symm

omit [SecondCountableTopology G] [CompactSpace m.toMonoidHom.ker] in
private theorem bruhat_support_iff_ae [ν.IsOpenPosMeasure] {I R : Set ℝ}
    (a : I) (hR : IsClosed R) (f : E[I]) :
    tsupport f.val ⊆ modulatedLog m ⁻¹' R ↔
      ∀ᵐ g ∂H, modulatedLog m g ∉ R → f.val g = 0 := by
  constructor
  · intro h
    exact Eventually.of_forall fun g hg =>
      image_eq_zero_of_notMem_tsupport (fun hs => hg (h hs))
  · intro h
    letI : (H).IsOpenPosMeasure := splitHaar_openPos m τ hτ ν
    have hm : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
    apply closure_minimal _ (hR.preimage hm)
    intro g hg
    by_contra hn
    have ho : IsOpen (modulatedLog m ⁻¹' R)ᶜ := (hR.preimage hm).isOpen_compl
    have hz : f.val =ᵐ[(H).restrict (modulatedLog m ⁻¹' R)ᶜ] (0 : G → ℂ) :=
      (ae_restrict_iff' ho.measurableSet).mpr h
    exact hg (Measure.eqOn_open_of_ae_eq hz ho
      (bruhatDecay_continuous_val m a f).continuousOn continuous_const.continuousOn hn)

/-- The right-half-line norm on the genuine Bruhat tests is finite exactly
on the nonpositive logarithmic support subspace. There it equals the endpoint norm. -/
theorem bruhatRightHalfLine_norm [ν.IsOpenPosMeasure] {I : Set ℝ} {a : ℝ}
    (ha : a ∈ I) (s : ℝ) (f : E[I]) :
    (N[Ici a,s] f.val ≠ ⊤ ↔ tsupport f.val ⊆ modulatedLog m ⁻¹' Iic 0) ∧
    (tsupport f.val ⊆ modulatedLog m ⁻¹' Iic 0 →
      N[Ici a,s] f.val = ‖bruhatCompactIntervalGroupInclusion m τ hτ ν ha ha le_rfl s f‖ₑ) := by
  have hm : Measurable (modulatedLog m) := (continuous_toAdd.comp m.continuous).measurable
  have hf := (bruhatDecay_continuous_val m ⟨a, ha⟩ f).measurable
  have hs := bruhat_support_iff_ae m τ hτ ν ⟨a, ha⟩ (isClosed_Iic (a := (0 : ℝ))) f
  have he (h : tsupport f.val ⊆ modulatedLog m ⁻¹' Iic 0) :
      N[Ici a,s] f.val = ‖bruhatCompactIntervalGroupInclusion m τ hτ ν ha ha le_rfl s f‖ₑ := by
    rw [hardySobolevIntervalENorm_Ici_of_ae H hm hf
      ((hs.mp h).mono fun _ hg hx => hg (not_le_of_gt hx)) a s,
      bruhatEndpoint_eLpNorm m τ hτ ν ha]
  refine ⟨⟨fun h => hs.mpr ?_, fun h => (he h).trans_ne ENNReal.coe_ne_top⟩, he⟩
  by_contra hn
  apply h (hardySobolevIntervalENorm_Ici_eq_top H hm hf ?_ a s)
  simpa only [ae_iff, Set.compl_ofPred, Classical.not_imp, notMem_Iic] using hn

/-- The left-half-line norm on the genuine Bruhat tests is finite exactly
on the nonnegative logarithmic support subspace. There it equals the endpoint norm. -/
theorem bruhatLeftHalfLine_norm [ν.IsOpenPosMeasure] {I : Set ℝ} {b : ℝ}
    (hb : b ∈ I) (s : ℝ) (f : E[I]) :
    (N[Iic b,s] f.val ≠ ⊤ ↔ tsupport f.val ⊆ modulatedLog m ⁻¹' Ici 0) ∧
    (tsupport f.val ⊆ modulatedLog m ⁻¹' Ici 0 →
      N[Iic b,s] f.val = ‖bruhatCompactIntervalGroupInclusion m τ hτ ν hb hb le_rfl s f‖ₑ) := by
  have hm : Measurable (modulatedLog m) := (continuous_toAdd.comp m.continuous).measurable
  have hf := (bruhatDecay_continuous_val m ⟨b, hb⟩ f).measurable
  have hs := bruhat_support_iff_ae m τ hτ ν ⟨b, hb⟩ (isClosed_Ici (a := (0 : ℝ))) f
  have he (h : tsupport f.val ⊆ modulatedLog m ⁻¹' Ici 0) :
      N[Iic b,s] f.val = ‖bruhatCompactIntervalGroupInclusion m τ hτ ν hb hb le_rfl s f‖ₑ := by
    rw [hardySobolevIntervalENorm_Iic_of_ae H hm hf
      ((hs.mp h).mono fun _ hg hx => hg (not_le_of_gt hx)) b s,
      bruhatEndpoint_eLpNorm m τ hτ ν hb]
  refine ⟨⟨fun h => hs.mpr ?_, fun h => (he h).trans_ne ENNReal.coe_ne_top⟩, he⟩
  by_contra hn
  apply h (hardySobolevIntervalENorm_Iic_eq_top H hm hf ?_ b s)
  simpa only [ae_iff, Set.compl_ofPred, Classical.not_imp, notMem_Ici] using hn


/-- Density passes from strict support inside an open set to an additional
support constraint whose boundary has zero measure. -/
private theorem bruhatSupportedEndpoint_closure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {b : ℝ} (hb : b ∈ I) (s : ℝ) {U V R : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hVR : V ⊆ R)
    (hnull : ∀ᵐ g ∂W[b,s], modulatedLog m g ∈ V ↔ modulatedLog m g ∈ R) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (U ∩ R) =>
      bruhatCompactIntervalGroupInclusion m τ hτ ν hb hb le_rfl s f.val)) =
    {u | ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ R → u g = 0} := by
  let J := bruhatCompactIntervalGroupInclusion m τ hτ ν hb hb le_rfl s
  have h := bruhatCompactIntervalGroupCutoff_closure m τ hτ ν hm hb hb le_rfl s (hU.inter hV)
  change closure (range (fun f : bruhatIntervalCutoffTests m I (U ∩ V) => J f.val)) = _ at h
  have he : {u : Lp ℂ 2 W[b,s] | ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ V → u g = 0} =
      {u : Lp ℂ 2 W[b,s] | ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ R → u g = 0} := by
    ext u
    change (∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ V → u g = 0) ↔
      (∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ R → u g = 0)
    exact eventually_congr (hnull.mono fun g hg => by simp only [mem_inter_iff, hg])
  apply le_antisymm
  · apply closure_minimal _ ((h.trans he) ▸ isClosed_closure)
    rintro _ ⟨f, rfl⟩
    change ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ R → J f.val g = 0
    filter_upwards [bruhatCompactIntervalGroupInclusion_ae m τ hτ ν hb hb le_rfl s f.val]
      with g hg hnot
    exact hg.trans (image_eq_zero_of_notMem_tsupport (fun hf => hnot (f.property hf)))
  · rw [← he, ← h]
    apply closure_mono
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨f.val, f.property.trans (preimage_mono (inter_subset_inter_right U hVR))⟩, rfl⟩

/-- Complete the finite-norm tests on a right-half-line abscissa base,
with any additional strict radial cutoff. -/
theorem bruhatRightHalfLine_cutoff_closure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a : ℝ} (ha : a ∈ I) (s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (U ∩ Iic 0) =>
      bruhatCompactIntervalGroupInclusion m τ hτ ν ha ha le_rfl s f.val)) =
    {u | ∀ᵐ g ∂W[a,s], modulatedLog m g ∉ U ∩ Iic 0 → u g = 0} := by
  apply bruhatSupportedEndpoint_closure m τ hτ ν hm ha s hU isOpen_Iio Iio_subset_Iic_self
  filter_upwards [modulatedCompactInterval_log_ae_ne m τ hτ ν (a := a) le_rfl s 0] with g hg
  change modulatedLog m g < 0 ↔ modulatedLog m g ≤ 0
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hg⟩

/-- Complete the finite-norm tests on a left-half-line abscissa base,
with any additional strict radial cutoff. -/
theorem bruhatLeftHalfLine_cutoff_closure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {b : ℝ} (hb : b ∈ I) (s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (U ∩ Ici 0) =>
      bruhatCompactIntervalGroupInclusion m τ hτ ν hb hb le_rfl s f.val)) =
    {u | ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U ∩ Ici 0 → u g = 0} := by
  apply bruhatSupportedEndpoint_closure m τ hτ ν hm hb s hU isOpen_Ioi Ioi_subset_Ici_self
  filter_upwards [modulatedCompactInterval_log_ae_ne m τ hτ ν (a := b) le_rfl s 0] with g hg
  change 0 < modulatedLog m g ↔ 0 ≤ modulatedLog m g
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hg.symm⟩

/-- For a whole-line base the only finite-norm Bruhat test is zero. -/
theorem bruhatWholeLine_finite_iff [ν.IsOpenPosMeasure] {I : Set ℝ} {a : ℝ}
    (ha : a ∈ I) (s : ℝ) (f : E[I]) :
    N[univ,s] f.val ≠ ⊤ ↔ f = 0 := by
  constructor
  · intro hf
    have hmono (J : Set ℝ) : N[J,s] f.val ≤ N[univ,s] f.val := by
      exact iSup₂_le fun b c => le_iSup₂_of_le
        ⟨(b : ℝ), mem_univ _⟩ ⟨(c : ℝ), mem_univ _⟩ le_rfl
    have hR := (bruhatRightHalfLine_norm m τ hτ ν ha s f).1.mp
      (ne_top_of_le_ne_top hf (hmono (Ici a)))
    have hL := (bruhatLeftHalfLine_norm m τ hτ ν ha s f).1.mp
      (ne_top_of_le_ne_top hf (hmono (Iic a)))
    have hn : ∀ᵐ g ∂H, modulatedLog m g ≠ 0 := by
      let e := intervalGroupChart m τ hτ
      have he := intervalGroupChart_preserving m τ hτ ν (volume : Measure ℝ)
      have hc : MeasurePreserving e (ν.prod (volume : Measure ℝ)) H := he
      have hpre := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := volume)).ae
        ((volume : Measure ℝ).ae_ne (0 : ℝ))
      filter_upwards [(hc.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hpre] with g hg
      change (e.symm g).2 ≠ 0 at hg
      rw [← intervalGroupChart_log m τ hτ (e.symm g),
        show e (e.symm g) = g from e.apply_symm_apply g] at hg
      exact hg
    have hz : f.val =ᵐ[H] (0 : G → ℂ) := by
      filter_upwards [hn] with g hg
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact hg (le_antisymm (hR hs) (hL hs))
    letI : (H).IsOpenPosMeasure := splitHaar_openPos m τ hτ ν
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    exact Measure.eq_of_ae_eq hz (bruhatDecay_continuous_val m ⟨a, ha⟩ f) continuous_const
  · rintro rfl
    change hardySobolevIntervalENorm H (modulatedLog m) univ s (0 : G → ℂ) ≠ ⊤
    simp [hardySobolevIntervalENorm]


omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CompactSpace m.toMonoidHom.ker] [IsFiniteMeasure ν] in
/-- A closed representative of a cutoff gives its indicator projection
provided it differs from the strict-support cutoff only by a null set. -/
private theorem endpointClosedCutoff_indicator {b s : ℝ} {U S : Set ℝ}
    (hS : MeasurableSet S) (he : ∀ᵐ g ∂W[b,s], modulatedLog m g ∈ U ↔ modulatedLog m g ∈ S) :
    ∃ P : Lp ℂ 2 W[b,s] →L[ℂ] Lp ℂ 2 W[b,s],
      IsClosed (range P) ∧ (∀ u, P (P u) = P u) ∧
      (∀ u, (P u : G → ℂ) =ᵐ[W[b,s]] (modulatedLog m ⁻¹' S).indicator (u : G → ℂ)) ∧
      range P = {u | ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U → u g = 0} := by
  let A := modulatedLog m ⁻¹' S
  have hA : MeasurableSet A := (continuous_toAdd.comp m.continuous).measurable hS
  obtain ⟨P, hc, _, hP⟩ := lpTwo_measurableCutoff (μ := W[b,s]) hA
  refine ⟨P, hc, fun u => (hP u).1, fun u => (hP u).2, ?_⟩
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    filter_upwards [(hP v).2, he] with g h₁ h₂ hn
    exact h₁.trans (indicator_of_notMem (show g ∉ A from fun hs => hn (h₂.mpr hs)) _)
  · intro h
    refine ⟨u, Lp.ext ?_⟩
    filter_upwards [h, (hP u).2, he] with g hg hp h₁
    by_cases hm : g ∈ A
    · exact hp.trans (indicator_of_mem hm _)
    · exact hp.trans ((indicator_of_notMem hm _).trans (hg (fun hu => hm (h₁.mp hu))).symm)

/-- The two half-line completions use the lower cutoff indicator relative
to their respective finite-norm support rays. -/
theorem bruhatHalfLine_lowerIndicator [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {b : ℝ} (hb : b ∈ I) (s c : ℝ)
    (R : Set ℝ) (hR : R = Iic 0 ∨ R = Ici 0) :
    ∃ P : Lp ℂ 2 W[b,s] →L[ℂ] Lp ℂ 2 W[b,s],
      IsClosed (range P) ∧ (∀ u, P (P u) = P u) ∧
      (∀ u, (P u : G → ℂ) =ᵐ[W[b,s]]
        (modulatedLog m ⁻¹' (Ici c ∩ R)).indicator (u : G → ℂ)) ∧
      closure (range (fun f : bruhatIntervalCutoffTests m I (Ioi c ∩ R) =>
        bruhatCompactIntervalGroupInclusion m τ hτ ν hb hb le_rfl s f.val)) = range P := by
  have hSm : MeasurableSet (Ici c ∩ R) := by
    rcases hR with rfl | rfl
    · exact measurableSet_Ici.inter measurableSet_Iic
    · exact measurableSet_Ici.inter measurableSet_Ici
  have he : ∀ᵐ g ∂W[b,s], modulatedLog m g ∈ Ioi c ∩ R ↔
      modulatedLog m g ∈ Ici c ∩ R := by
    filter_upwards [modulatedCompactInterval_log_ae_ne m τ hτ ν (a := b) le_rfl s c] with g hg
    have hh : c < modulatedLog m g ↔ c ≤ modulatedLog m g :=
      ⟨le_of_lt, fun h => lt_of_le_of_ne h hg.symm⟩
    simp only [mem_inter_iff, mem_Ioi, mem_Ici, hh]
  obtain ⟨P, hc, hp, hp', hpr⟩ := endpointClosedCutoff_indicator m τ hτ ν hSm he
  refine ⟨P, hc, hp, hp', hpr.symm ▸ ?_⟩
  rcases hR with rfl | rfl
  · exact bruhatRightHalfLine_cutoff_closure m τ hτ ν hm hb s isOpen_Ioi
  · exact bruhatLeftHalfLine_cutoff_closure m τ hτ ν hm hb s isOpen_Ioi

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CompactSpace m.toMonoidHom.ker] in
/-- The source exact sequence holds relative to a measurable radial support.
The physical maps are inclusion and multiplication by the upper-ray indicator. -/
theorem bruhatInterval_physicalExact_relative {a b : ℝ} (hab : a ≤ b) (s c : ℝ) (hc : c ≤ 0)
    (R : Set ℝ) (hR : MeasurableSet R) :
    let W := hardySobolevMeasure H (modulatedLog m) a b s
    let E := Lp ℂ 2 W
    let S := fun (U : Set ℝ) =>
      {f : E | (f : G → ℂ) =ᵐ[W] (modulatedLog m ⁻¹' (U ∩ R)).indicator (f : G → ℂ)}
    ∃ (L M Q : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] Q),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (Q : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : G → ℂ) =ᵐ[W]
        (modulatedLog m ⁻¹' (Ici 0 ∩ R)).indicator (f.val : G → ℂ)) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  exact lpTwo_cutoff_exact_relative (hardySobolevMeasure H (modulatedLog m) a b s)
    (modulatedLog m) (continuous_toAdd.comp m.continuous).measurable c hc
    (modulatedCompactInterval_log_ae_ne m τ hτ ν hab s 0) R hR


abbrev bruhatHalfLine_physicalExact (b s c : ℝ) (hc : c ≤ 0)
    (R : Set ℝ) (hR : MeasurableSet R) :=
  bruhatInterval_physicalExact_relative m τ hτ ν (a := b) le_rfl s c hc R hR

/-- The character and logarithmic derivative factors in the group Mellin integral. -/
def bruhatGroupMellinIntegrand (χ : PontryaginDual m.toMonoidHom.ker)
    (f : G → ℂ) (k : ℕ) (z : ℂ) (g : G) : ℂ :=
  (χ ((intervalGroupChart m τ hτ).symm g).1 : ℂ) *
    f g * mellinEvaluationKernel k z (modulatedLog m g)

/-- Character Mellin moments as integrals on the original group. -/
def bruhatGroupMellinMoment (χ : PontryaginDual m.toMonoidHom.ker)
    (f : G → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ g, bruhatGroupMellinIntegrand m τ hτ χ f k z g ∂H

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CompactSpace m.toMonoidHom.ker] in
private theorem endpointGroupMellin_analytic (b s : ℝ)
    {U J : Set ℝ} (hU : IsOpen U) (hJ : IsOpen J)
    (hK : ∀ w : ℂ, w.re ∈ J → ∀ k : ℕ,
      MemLp (U.indicator (mellinEvaluationKernel k w)) 2 (stripMeasure (-b) (-b) (-s)))
    (χ : PontryaginDual m.toMonoidHom.ker) (f : Lp ℂ 2 W[b,s])
    (hf : ∀ᵐ g ∂W[b,s], modulatedLog m g ∉ U → f g = 0) (k : ℕ)
    {z : ℂ} (hz : z.re ∈ J) :
    Integrable (bruhatGroupMellinIntegrand m τ hτ χ f k z) H ∧
      AnalyticAt ℂ (bruhatGroupMellinMoment m τ hτ ν χ f 0) z ∧
      iteratedDeriv k (bruhatGroupMellinMoment m τ hτ ν χ f 0) z =
        bruhatGroupMellinMoment m τ hτ ν χ f k z := by
  obtain ⟨u, hu⟩ := exists_modulatedIntervalGroupProfile_ae m τ hτ ν
    (a := b) (b := b) le_rfl f hf
  have hAC : H ≪ W[b,s] := by
    unfold hardySobolevMeasure
    apply withDensity_absolutelyContinuous'
    · exact (((continuous_hardySobolevWeight b b s).measurable.comp
        (continuous_toAdd.comp m.continuous).measurable).ennreal_ofReal).aemeasurable
    · exact .of_forall fun g => ENNReal.ofReal_ne_zero_iff.mpr (by unfold hardySobolevWeight; positivity)
  have hIntegrand (n : ℕ) (w : ℂ) :
      bruhatGroupMellinIntegrand m τ hτ χ (modulatedIntervalGroupProfile m τ hτ ν b b s u) n w
        =ᵐ[H] bruhatGroupMellinIntegrand m τ hτ χ f n w := by
    filter_upwards [hAC.ae_le hu] with g hg
    unfold bruhatGroupMellinIntegrand
    rw [hg]
  have hM (n : ℕ) (w : ℂ) (hw : w.re ∈ J) :
      modulatedIntervalMoment ν b b s χ u n w = bruhatGroupMellinMoment m τ hτ ν χ f n w :=
    (modulatedIntervalMoment_onGroup m τ hτ ν b b s hU χ n w (hK w hw n) u).2.trans
      (integral_congr_ae (hIntegrand n w))
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, w.re ∈ J :=
    (hJ.preimage Complex.continuous_re).mem_nhds hz
  have hEq : modulatedIntervalMoment ν b b s χ u 0 =ᶠ[𝓝 z]
      bruhatGroupMellinMoment m τ hτ ν χ f 0 := hnear.mono fun w hw => hM 0 w hw
  have hInt := (modulatedIntervalMoment_onGroup m τ hτ ν b b s hU χ k z (hK z hz k) u).1
  obtain ⟨hA, hD⟩ := modulatedIntervalMoment_analyticOnAbscissae ν b b s hU χ u hJ hK k hz
  exact ⟨hInt.congr (hIntegrand k z), hA.congr hEq,
    (hEq.iteratedDeriv_eq k).symm.trans (hD.trans (hM k z hz))⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CompactSpace m.toMonoidHom.ker] in
/-- Completed right-half-line classes have holomorphic group Mellin
transforms on the open right half-plane. -/
theorem bruhatRightHalfLine_mellin_analytic (b s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual m.toMonoidHom.ker) (f : Lp ℂ 2 W[b,s])
    (hf : ∀ᵐ g ∂W[b,s], 0 < modulatedLog m g → f g = 0) (k : ℕ)
    {z : ℂ} (hz : b < z.re) :
    Integrable (bruhatGroupMellinIntegrand m τ hτ χ f k z) H ∧
      AnalyticAt ℂ (bruhatGroupMellinMoment m τ hτ ν χ f 0) z ∧
      iteratedDeriv k (bruhatGroupMellinMoment m τ hτ ν χ f 0) z =
        bruhatGroupMellinMoment m τ hτ ν χ f k z := by
  refine endpointGroupMellin_analytic m τ hτ ν b s isOpen_Iio isOpen_Ioi
    (fun w (hw : b < w.re) n => (supportedMellinEvaluation_memLp_iff b b s isOpen_Iio n w).mp
      ((hardySobolev_right_mellinEvaluation_exists_iff hw.le hs n).mpr (Or.inl hw))) χ f ?_ k hz
  filter_upwards [hf, modulatedCompactInterval_log_ae_ne m τ hτ ν (a := b) le_rfl s 0]
    with g hg hn h
  exact hg (lt_of_le_of_ne (le_of_not_gt h) hn.symm)

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CompactSpace m.toMonoidHom.ker] in
/-- Completed left-half-line classes have holomorphic group Mellin
transforms on the open left half-plane. -/
theorem bruhatLeftHalfLine_mellin_analytic (b s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual m.toMonoidHom.ker) (f : Lp ℂ 2 W[b,s])
    (hf : ∀ᵐ g ∂W[b,s], modulatedLog m g < 0 → f g = 0) (k : ℕ)
    {z : ℂ} (hz : z.re < b) :
    Integrable (bruhatGroupMellinIntegrand m τ hτ χ f k z) H ∧
      AnalyticAt ℂ (bruhatGroupMellinMoment m τ hτ ν χ f 0) z ∧
      iteratedDeriv k (bruhatGroupMellinMoment m τ hτ ν χ f 0) z =
        bruhatGroupMellinMoment m τ hτ ν χ f k z := by
  refine endpointGroupMellin_analytic m τ hτ ν b s isOpen_Ioi isOpen_Iio
    (fun w (hw : w.re < b) n => (supportedMellinEvaluation_memLp_iff b b s isOpen_Ioi n w).mp
      ((hardySobolev_left_mellinEvaluation_exists_iff hw.le hs n).mpr (Or.inl hw))) χ f ?_ k hz
  filter_upwards [hf, modulatedCompactInterval_log_ae_ne m τ hτ ν (a := b) le_rfl s 0]
    with g hg hn h
  exact hg (lt_of_le_of_ne (le_of_not_gt h) hn)

end
end Masullo
