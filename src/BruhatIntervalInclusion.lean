import BruhatSplitSchwartz
import ModulatedSobolevContinuity
import ModulatedIntervalTraces
import BruhatDecayRestriction
import ModulatedExponentialRadial
import ModulatedSobolevTests

open Filter Function MeasureTheory Set Topology
open scoped ENNReal SchwartzMap

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

local notation "K" => m.toMonoidHom.ker
local notation "E[" I "]" => ModulatedExponentialInductive m I

private def intervalTestTwist {I : Set ℝ} (t : I) : E[I] →L[ℂ] 𝓢(ℝ, C(K, ℂ)) :=
  (exists_bruhatSplitSchwartz m τ hτ).choose.comp (modulatedDecayTwistCLM m I t)

omit [MeasurableSpace G] [BorelSpace G] in
private theorem intervalTestTwist_apply {I : Set ℝ} (t : I) (f : E[I]) (x : ℝ) (k : K) :
    intervalTestTwist m τ hτ t f x k =
      (Real.exp ((t : ℝ) * x) : ℂ) * f.val (τ (Multiplicative.ofAdd x) * k.val) := by
  let g := τ (Multiplicative.ofAdd x) * k.val
  have h := (exists_bruhatSplitSchwartz m τ hτ).choose_spec
    (modulatedDecayTwistCLM m I t f) x k
  change intervalTestTwist m τ hτ t f x k = modulatedExponentialWeight m t f.val g at h
  have hg : (m g).toAdd = x := by
    dsimp only [g]
    rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one]
    rfl
  simpa only [modulatedExponentialWeight_apply, hg, Complex.real_smul] using h

private def polynomialAmplitude (s : ℝ) (x : ℝ) : ℂ := ((1 + x ^ 2) ^ (s / 4) : ℝ)

private theorem polynomialAmplitude_temperate (s : ℝ) : (polynomialAmplitude s).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp (by
    simpa only [Real.norm_eq_abs, sq_abs] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 4))

private def endpointAmplitude (b s : ℝ) (p : K × ℝ) : ℝ :=
  stripSobolevAmplitude b b s p.2

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [CompactSpace K] in
private theorem endpointAmplitude_measurable (b s : ℝ) :
    Measurable (endpointAmplitude m b s) :=
  (stripSobolevAmplitude_continuous b b s).measurable.comp measurable_snd

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace K] in
private theorem endpointAmplitude_pos (b s : ℝ) (p : K × ℝ) :
    0 < endpointAmplitude m b s p := stripSobolevAmplitude_pos ..

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [CompactSpace K] [IsFiniteMeasure ν] in
private theorem endpointAmplitude_measure (b s : ℝ) :
    ν.prod (stripMeasure b b s) = amplitudeMeasure (ν.prod volume) (endpointAmplitude m b s) := by
  unfold stripMeasure amplitudeMeasure
  exact prod_withDensity_right
    (((stripSobolevAmplitude_continuous b b s).pow 2).measurable.ennreal_ofReal)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [CompactSpace K] [IsFiniteMeasure ν] in
private theorem endpointAmplitudePreserving (b s : ℝ) :
    MeasurePreserving (id : K × ℝ → K × ℝ) (ν.prod (stripMeasure b b s))
      (amplitudeMeasure (ν.prod volume) (endpointAmplitude m b s)) :=
  ⟨measurable_id, by simpa only [Measure.map_id] using endpointAmplitude_measure m ν b s⟩

/-- Every abscissa in the decay interval gives a continuous weighted L²
evaluation on the original Bruhat decay space, at any real Sobolev order. -/
def bruhatIntervalEndpointInclusion {I : Set ℝ} (b : I) (s : ℝ) :
    E[I] →L[ℂ] Lp ℂ 2 (ν.prod (stripMeasure b b s)) :=
  ((Lp.compMeasurePreservingₗᵢ ℂ id (endpointAmplitudePreserving m ν b s)).toContinuousLinearMap).comp
    (((amplitudeL2Iso (ν.prod volume) (endpointAmplitude m b s)
        (endpointAmplitude_measurable m b s) (endpointAmplitude_pos m b s)).symm.toLinearIsometry.toContinuousLinearMap).comp
      ((schwartzEvaluateCLM ν).comp
        ((SchwartzMap.smulLeftCLM C(K, ℂ) (polynomialAmplitude s)).comp
          (intervalTestTwist m τ hτ b))))

theorem bruhatIntervalEndpointInclusion_ae {I : Set ℝ} (b : I) (s : ℝ) (f : E[I]) :
    (bruhatIntervalEndpointInclusion m τ hτ ν b s f : K × ℝ → ℂ)
      =ᵐ[ν.prod (stripMeasure b b s)] fun p => f.val (τ (Multiplicative.ofAdd p.2) * p.1.val) := by
  let F := SchwartzMap.smulLeftCLM C(K, ℂ) (polynomialAmplitude s) (intervalTestTwist m τ hτ b f)
  let A := amplitudeL2Iso (ν.prod volume) (endpointAmplitude m b s)
    (endpointAmplitude_measurable m b s) (endpointAmplitude_pos m b s)
  let v := schwartzEvaluateCLM ν F
  have h₁ := Lp.coeFn_compMeasurePreserving (A.symm v) (endpointAmplitudePreserving m ν b s)
  have h₂ := amplitudeL2Iso_symm_ae (ν.prod volume) (endpointAmplitude m b s)
    (endpointAmplitude_measurable m b s) (endpointAmplitude_pos m b s) v
  have h₃ := (amplitudeMeasure_absolutelyContinuous (ν.prod volume)
    (endpointAmplitude m b s)).ae_le (schwartzEvaluateCLM_ae ν F)
  have he := (endpointAmplitude_measure m ν (b : ℝ) s).le.absolutelyContinuous
  filter_upwards [h₁, he.ae_le h₂, he.ae_le h₃] with p h₁ h₂ h₃
  change (bruhatIntervalEndpointInclusion m τ hτ ν b s f) p = (A.symm v) p at h₁
  rw [h₁, h₂, h₃, show F p.2 = _ from SchwartzMap.smulLeftCLM_apply_apply
    (polynomialAmplitude_temperate s) _ _, ContinuousMap.smul_apply, intervalTestTwist_apply]
  have hr : (endpointAmplitude m b s p : ℂ) =
      polynomialAmplitude s p.2 * (Real.exp ((b : ℝ) * p.2) : ℂ) := by
    simp only [endpointAmplitude, stripSobolevAmplitude, ite_self, polynomialAmplitude,
      Complex.ofReal_mul]
    ring
  rw [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul, ← mul_assoc (polynomialAmplitude s p.2),
    ← hr, ← mul_assoc, inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (endpointAmplitude_pos m b s p).ne'), one_mul]


private def intervalTestProfile {I : Set ℝ} :
    E[I] →ₗ[ℂ] (K × ℝ → ℂ) where
  toFun f p := f.val (τ (Multiplicative.ofAdd p.2) * p.1.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hτ in
private theorem intervalTestProfile_memLp {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) (f : E[I]) :
    MemLp (intervalTestProfile m τ f) 2 (ν.prod (stripMeasure a b s)) := by
  obtain ⟨_, _, hle⟩ := modulatedInterval_endpointMeasures ν hab s
  have hA := (Lp.memLp (bruhatIntervalEndpointInclusion m τ hτ ν ⟨a, ha⟩ s f)).ae_eq
    (bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨a, ha⟩ s f)
  have hB := (Lp.memLp (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f)).ae_eq
    (bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨b, hb⟩ s f)
  refine MemLp.mono_measure hle ?_
  apply (memLp_two_iff_integrable_sq_norm (hA.aestronglyMeasurable.add_measure
    hB.aestronglyMeasurable)).mpr
  exact ((memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA).add_measure
    ((memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB)

private def intervalTestInclusionLinear {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) :
    E[I] →ₗ[ℂ] Lp ℂ 2 (ν.prod (stripMeasure a b s)) where
  toFun f := (intervalTestProfile_memLp m τ hτ ν ha hb hab s f).toLp (intervalTestProfile m τ f)
  map_add' f g := by
    let hf := intervalTestProfile_memLp m τ hτ ν ha hb hab s f
    let hg := intervalTestProfile_memLp m τ hτ ν ha hb hab s g
    apply Lp.ext
    filter_upwards [(intervalTestProfile_memLp m τ hτ ν ha hb hab s (f + g)).coeFn_toLp,
      hf.coeFn_toLp, hg.coeFn_toLp, Lp.coeFn_add (hf.toLp _) (hg.toLp _)] with p h hp hq hsum
    rw [h, hsum, Pi.add_apply, hp, hq, map_add, Pi.add_apply]
  map_smul' c f := by
    let hf := intervalTestProfile_memLp m τ hτ ν ha hb hab s f
    apply Lp.ext
    filter_upwards [(intervalTestProfile_memLp m τ hτ ν ha hb hab s (c • f)).coeFn_toLp,
      hf.coeFn_toLp, Lp.coeFn_smul c (hf.toLp _)] with p h hp hc
    rw [RingHom.id_apply, h, hc, Pi.smul_apply, hp, map_smul, Pi.smul_apply]

/-- The weighted inclusion over a compact interval is continuous for the
original Bruhat inductive topology. Only the two endpoint twists are needed. -/
def bruhatCompactIntervalInclusion {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) :
    E[I] →L[ℂ] Lp ℂ 2 (ν.prod (stripMeasure a b s)) := by
  let L := intervalTestInclusionLinear m τ hτ ν ha hb hab s
  let A := bruhatIntervalEndpointInclusion m τ hτ ν ⟨a, ha⟩ s
  let B := bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s
  have hbounds := modulatedInterval_endpointMeasures ν hab s
  have hleA := hbounds.1
  have hleB := hbounds.2.1
  have hle := hbounds.2.2
  have hR (f : E[I]) : (L f : K × ℝ → ℂ) =ᵐ[ν.prod (stripMeasure a b s)]
      intervalTestProfile m τ f :=
    (intervalTestProfile_memLp m τ hτ ν ha hb hab s f).coeFn_toLp
  have hA (f : E[I]) : lpTwoMeasureInclusion hleA (L f) = A f := Lp.ext (by
    filter_upwards [lpTwoMeasureInclusion_ae hleA (L f), hleA.absolutelyContinuous.ae_le (hR f),
      bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨a, ha⟩ s f] with p h₁ h₂ h₃
    exact h₁.trans (h₂.trans h₃.symm))
  have hB (f : E[I]) : lpTwoMeasureInclusion hleB (L f) = B f := Lp.ext (by
    filter_upwards [lpTwoMeasureInclusion_ae hleB (L f), hleB.absolutelyContinuous.ae_le (hR f),
      bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨b, hb⟩ s f] with p h₁ h₂ h₃
    exact h₁.trans (h₂.trans h₃.symm))
  have hnorm (f : E[I]) : ‖L f‖ ≤ ‖A f‖ + ‖B f‖ := by
    have hsq := lpTwo_norm_sq_le_endpoints hleA hleB hle (L f)
    rw [hA, hB] at hsq
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    exact hsq.trans (by nlinarith [mul_nonneg (norm_nonneg (A f)) (norm_nonneg (B f))])
  refine ⟨L, continuous_of_continuousAt_zero L ?_⟩
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hnorm
  simpa only [map_zero, norm_zero, add_zero] using
    (A.continuous.norm.tendsto (0 : E[I])).add (B.continuous.norm.tendsto (0 : E[I]))

theorem bruhatCompactIntervalInclusion_ae {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) (f : E[I]) :
    (bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s f : K × ℝ → ℂ)
      =ᵐ[ν.prod (stripMeasure a b s)] fun p => f.val (τ (Multiplicative.ofAdd p.2) * p.1.val) := by
  show ((intervalTestInclusionLinear m τ hτ ν ha hb hab s f : Lp ℂ 2 _) : K × ℝ → ℂ)
    =ᵐ[ν.prod (stripMeasure a b s)] intervalTestProfile m τ f
  exact (intervalTestProfile_memLp m τ hτ ν ha hb hab s f).coeFn_toLp


/-- Bruhat decay tests with topological support strictly inside the radial cutoff. -/
def bruhatIntervalCutoffTests (I U : Set ℝ) : Submodule ℂ E[I] where
  carrier := {f | tsupport f.val ⊆ modulatedLog m ⁻¹' U}
  zero_mem' := by change tsupport (0 : G → ℂ) ⊆ _; simp
  add_mem' hf hg := (tsupport_add _ _).trans (union_subset hf hg)
  smul_mem' c _ hf := (tsupport_smul_subset_right (fun _ : G => c) _).trans hf

/-- The cutoff inclusion uses the same functions as the ambient weighted inclusion. -/
def bruhatCompactIntervalCutoffInclusion {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) (U : Set ℝ) :
    bruhatIntervalCutoffTests m I U →L[ℂ] lpTwoRadialSupport ν (stripMeasure a b s) U :=
  ((bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s).comp
    (bruhatIntervalCutoffTests m I U).subtypeL).codRestrict _ (fun f => by
      change ∀ᵐ p ∂ν.prod (stripMeasure a b s), p.2 ∉ U →
        bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s f.val p = 0
      filter_upwards [bruhatCompactIntervalInclusion_ae m τ hτ ν ha hb hab s f.val] with p hp hU
      rw [hp]
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hlog : modulatedLog m (τ (Multiplicative.ofAdd p.2) * p.1.val) = p.2 := by
        change (m (τ (Multiplicative.ofAdd p.2) * p.1.val)).toAdd = p.2
        rw [map_mul, hτ, show m p.1.val = 1 from p.1.property, mul_one]
        rfl
      exact hU (hlog ▸ f.property hs))

set_option maxHeartbeats 1100000 in
private theorem intervalSeparatedTest_mem_range (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) (χ : PontryaginDual K) (f : compactRadialTests U) :
    modulatedIntervalSeparatedTest ν a b s hU χ f ∈
      range (bruhatCompactIntervalCutoffInclusion m τ hτ ν ha hb hab s U) := by
  obtain ⟨j, hj, _⟩ := exists_modulatedExponentialRadialIsotype m τ hτ χ⁻¹ hm
  let w : E[univ] := (j f.val).val
  let u : E[I] := modulatedDecay_restrict m (subset_univ I) w
  let e := modulatedLogSplit m τ hτ
  have hχ (x : ℝ) (k : K) :
      ((extendModulatedCharacter m τ hτ χ⁻¹ (e (x, k)))⁻¹ : Circle) = χ k := by
    change ((χ⁻¹) (e.symm (e (x, k))).2)⁻¹ = χ k
    rw [e.symm_apply_apply]
    exact inv_inv (χ k)
  have hup (x : ℝ) (k : K) : u.val (e (x, k)) = (χ k : ℂ) * f.val.val x := by
    have h := hj f.val (e (x, k))
    change u.val (e (x, k)) = _ at h
    have hx : (m (e (x, k))).toAdd = x := congrArg Prod.fst (e.symm_apply_apply (x, k))
    exact h.trans ((congrArg₂ (· * ·) (congrArg f.val.val hx)
      (congrArg (fun z : Circle => (z : ℂ)) (hχ x k))).trans (mul_comm _ _))
  have hs : tsupport u.val ⊆ modulatedLog m ⁻¹' tsupport f.val.val := by
    apply closure_minimal _ ((isClosed_tsupport _).preimage (continuous_toAdd.comp m.continuous))
    intro y hy
    contrapose! hy
    apply Function.notMem_support.mpr
    rw [show u.val y = _ from hj f.val y,
      image_eq_zero_of_notMem_tsupport (show (m y).toAdd ∉ tsupport f.val.val from hy), zero_mul]
  let v : bruhatIntervalCutoffTests m I U := ⟨u, hs.trans (preimage_mono f.property.2)⟩
  refine ⟨v, Subtype.ext (Lp.ext ?_)⟩
  have hval := bruhatCompactIntervalInclusion_ae m τ hτ ν ha hb hab s u
  filter_upwards [hval, modulatedIntervalSeparatedTest_ae ν a b s hU χ f] with p h₁ h₂
  exact h₁.trans ((hup p.2 p.1).trans h₂.symm)

/-- Strict-support Bruhat tests are dense in the weighted cutoff at any
real order and any two finite abscissae of the source decay space. -/
theorem bruhatCompactIntervalCutoff_dense [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) :
    DenseRange (bruhatCompactIntervalCutoffInclusion m τ hτ ν ha hb hab s U) := by
  let L := bruhatCompactIntervalCutoffInclusion m τ hτ ν ha hb hab s U
  have hspan : Submodule.span ℂ (range (fun p : PontryaginDual K × compactRadialTests U =>
      modulatedIntervalSeparatedTest ν a b s hU p.1 p.2)) ≤ L.toLinearMap.range :=
    Submodule.span_le.mpr (by
      rintro _ ⟨⟨χ, f⟩, rfl⟩
      exact intervalSeparatedTest_mem_range m τ hτ ν hm ha hb hab s hU χ f)
  have hclosure := Submodule.topologicalClosure_mono hspan
  rw [modulatedIntervalSeparatedTest_dense ν a b s hU] at hclosure
  exact dense_iff_closure_eq.mpr (congrArg SetLike.coe (top_le_iff.mp hclosure))


local notation "W[" a "," b "," s "]" =>
  hardySobolevMeasure (modulatedLogMeasure m τ hτ ν) (modulatedLog m) a b s

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [CompactSpace K] in
private theorem compactIntervalChart_preserving {a b s : ℝ} (hab : a ≤ b) :
    MeasurePreserving (intervalGroupChart m τ hτ) (ν.prod (stripMeasure a b s)) W[a,b,s] := by
  rw [← modulatedInterval_weightedHaar_split m τ hτ ν hab]
  exact intervalGroupChart_preserving m τ hτ ν (stripMeasure a b s)

private def intervalProductToGroup {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Lp ℂ 2 (ν.prod (stripMeasure a b s)) →ₗᵢ[ℂ] Lp ℂ 2 W[a,b,s] :=
  Lp.compMeasurePreservingₗᵢ ℂ (intervalGroupChart m τ hτ).symm
    ((compactIntervalChart_preserving m τ hτ ν (s := s) hab).symm
      (intervalGroupChart m τ hτ).toMeasurableEquiv)

/-- The compact-interval weighted Haar space is isometric to its split
product coordinates. -/
def bruhatCompactIntervalGroupProductEquiv {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Lp ℂ 2 W[a,b,s] ≃ₗᵢ[ℂ] Lp ℂ 2 (ν.prod (stripMeasure a b s)) := by
  let D := intervalProductToGroup m τ hτ ν hab s
  let e := intervalGroupChart m τ hτ
  have hmp := (compactIntervalChart_preserving m τ hτ ν (s := s) hab).symm e.toMeasurableEquiv
  have hd : Surjective D := by
    intro f
    obtain ⟨v, hv⟩ := exists_modulatedIntervalGroupProfile_ae m τ hτ ν hab
      (U := univ) f (by simp)
    exact ⟨v.val, Lp.ext ((Lp.coeFn_compMeasurePreserving v.val hmp).trans hv.symm)⟩
  exact (LinearIsometryEquiv.ofSurjective D hd).symm

theorem bruhatCompactIntervalGroupProductEquiv_ae {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : Lp ℂ 2 W[a,b,s]) :
    (bruhatCompactIntervalGroupProductEquiv m τ hτ ν hab s f : K × ℝ → ℂ)
      =ᵐ[ν.prod (stripMeasure a b s)] f ∘ intervalGroupChart m τ hτ := by
  let D := intervalProductToGroup m τ hτ ν hab s
  let J := bruhatCompactIntervalGroupProductEquiv m τ hτ ν hab s
  let e := intervalGroupChart m τ hτ
  have he := compactIntervalChart_preserving m τ hτ ν (s := s) hab
  have hj : D (J f) = f := J.symm_apply_apply f
  have h : (D (J f) : G → ℂ) =ᵐ[W[a,b,s]] J f ∘ e.symm :=
    Lp.coeFn_compMeasurePreserving (J f) (he.symm e.toMeasurableEquiv)
  rw [hj] at h
  filter_upwards [he.quasiMeasurePreserving.ae h] with p hp
  change f (e p) = J f (e.symm (e p)) at hp
  rw [e.symm_apply_apply] at hp
  exact hp.symm

/-- The continuous compact-interval inclusion in the weighted Haar space on G. -/
def bruhatCompactIntervalGroupInclusion {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) : E[I] →L[ℂ] Lp ℂ 2 W[a,b,s] :=
  (intervalProductToGroup m τ hτ ν hab s).toContinuousLinearMap.comp
    (bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s)

theorem bruhatCompactIntervalGroupInclusion_ae {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) (f : E[I]) :
    (bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f : G → ℂ) =ᵐ[W[a,b,s]] f.val := by
  let e := intervalGroupChart m τ hτ
  let J := bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s
  have hme := (compactIntervalChart_preserving m τ hτ ν (s := s) hab).symm e.toMeasurableEquiv
  filter_upwards [Lp.coeFn_compMeasurePreserving (J f) hme,
    hme.quasiMeasurePreserving.ae (bruhatCompactIntervalInclusion_ae m τ hτ ν ha hb hab s f)]
    with g hg hf
  have hchart (p : K × ℝ) : e p = τ (Multiplicative.ofAdd p.2) * p.1.val := rfl
  exact hg.trans (hf.trans (congrArg f.val ((hchart (e.symm g)).symm.trans (e.apply_symm_apply g))))

/-- The printed compact-interval supremum is the norm of the genuine
weighted Haar inclusion. -/
theorem bruhatCompactInterval_groupNorm {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) (f : E[I]) :
    hardySobolevIntervalENorm (modulatedLogMeasure m τ hτ ν) (modulatedLog m) (Icc a b) s f.val =
      ‖bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f‖ₑ := by
  rw [hardySobolevIntervalENorm_Icc _ _ hab, Lp.enorm_def]
  exact eLpNorm_congr_ae (bruhatCompactIntervalGroupInclusion_ae m τ hτ ν ha hb hab s f).symm

/-- On the group, ambient closure of the strict-support tests is precisely
almost-everywhere support in the logarithmic cutoff. -/
theorem bruhatCompactIntervalGroupCutoff_closure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatIntervalCutoffTests m I U =>
      bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f.val)) =
    {u | ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ U → u g = 0} := by
  let T := lpTwoRadialSupport ν (stripMeasure a b s) U
  let J := bruhatCompactIntervalCutoffInclusion m τ hτ ν ha hb hab s U
  let D := intervalProductToGroup m τ hτ ν hab s
  let e := intervalGroupChart m τ hτ
  have hT : IsClosed (T : Set (Lp ℂ 2 (ν.prod (stripMeasure a b s)))) := by
    obtain ⟨_, hclosed, _, _, _⟩ := modulatedInterval_radialProjection ν a b s hU
    exact hclosed
  let V : T → Lp ℂ 2 W[a,b,s] := fun v => D v.val
  have hV : IsClosedEmbedding V := D.isometry.isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
  change closure (range (V ∘ J)) = _
  rw [range_comp, hV.closure_image_eq,
    (bruhatCompactIntervalCutoff_dense m τ hτ ν hm ha hb hab s hU).closure_range, image_univ]
  have hme := (compactIntervalChart_preserving m τ hτ ν (s := s) hab).symm e.toMeasurableEquiv
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    have hv := hme.quasiMeasurePreserving.ae (v.property :
      ∀ᵐ p ∂ν.prod (stripMeasure a b s), p.2 ∉ U → v.val p = 0)
    filter_upwards [Lp.coeFn_compMeasurePreserving v.val hme, hv] with g hg hv hn
    have hlog : modulatedLog m g = (e.symm g).2 := by
      rw [← intervalGroupChart_log m τ hτ (e.symm g)]
      exact congrArg (modulatedLog m) (e.apply_symm_apply g).symm
    exact hg.trans (hv (hlog ▸ hn))
  · intro hu
    obtain ⟨v, hv⟩ := exists_modulatedIntervalGroupProfile_ae m τ hτ ν hab u hu
    exact ⟨v, Lp.ext ((Lp.coeFn_compMeasurePreserving v.val hme).trans hv.symm)⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [CompactSpace K] in
theorem modulatedCompactInterval_log_ae_ne {a b : ℝ} (hab : a ≤ b) (s c : ℝ) :
    ∀ᵐ g ∂W[a,b,s], modulatedLog m g ≠ c := by
  let e := intervalGroupChart m τ hτ
  have ha : ∀ᵐ x ∂stripMeasure a b s, x ≠ c :=
    (amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
      (stripSobolevAmplitude a b s)).ae_le ((volume : Measure ℝ).ae_ne c)
  have hp := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := stripMeasure a b s)).ae ha
  have he := (compactIntervalChart_preserving m τ hτ ν (s := s) hab).symm e.toMeasurableEquiv
  filter_upwards [he.quasiMeasurePreserving.ae hp] with g hg
  change (e.symm g).2 ≠ c at hg
  rw [← intervalGroupChart_log m τ hτ (e.symm g), show e (e.symm g) = g from e.apply_symm_apply g] at hg
  exact hg

/-- The physical cutoff clause for a compact interval base. The boundary
fiber is null, so the closed-ray multiplier gives the strict-support closure. -/
theorem bruhatCompactInterval_lowerIndicator [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s c : ℝ) :
    ∃ P : Lp ℂ 2 W[a,b,s] →L[ℂ] Lp ℂ 2 W[a,b,s],
      IsClosed (range P) ∧ (∀ u, P (P u) = P u) ∧
      (∀ u, (P u : G → ℂ) =ᵐ[W[a,b,s]] (modulatedLog m ⁻¹' Ici c).indicator (u : G → ℂ)) ∧
      closure (range (fun f : bruhatIntervalCutoffTests m I (Ioi c) =>
        bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f.val)) = range P := by
  let A := modulatedLog m ⁻¹' Ici c
  have hA : MeasurableSet A := (continuous_toAdd.comp m.continuous).measurable measurableSet_Ici
  obtain ⟨P, hc, _, hP⟩ := lpTwo_measurableCutoff (μ := W[a,b,s]) hA
  refine ⟨P, hc, fun u => (hP u).1, fun u => (hP u).2, ?_⟩
  rw [bruhatCompactIntervalGroupCutoff_closure m τ hτ ν hm ha hb hab s isOpen_Ioi]
  ext u
  constructor
  · intro h
    refine ⟨u, Lp.ext ?_⟩
    filter_upwards [h, (hP u).2] with g hg hp
    by_cases hm : g ∈ A
    · exact hp.trans (indicator_of_mem hm _)
    · have hn : modulatedLog m g ∉ Ioi c := by
        intro hi
        apply hm
        change c < modulatedLog m g at hi
        change c ≤ modulatedLog m g
        exact hi.le
      exact hp.trans ((indicator_of_notMem hm _).trans (hg hn).symm)
  · rintro ⟨v, rfl⟩
    filter_upwards [(hP v).2, modulatedCompactInterval_log_ae_ne m τ hτ ν hab s c] with g h ne hn
    exact h.trans (indicator_of_notMem (show g ∉ A from
      fun ha => hn (lt_of_le_of_ne ha ne.symm)) _)


/-- Both the entire-decay tests and any interval-decay space containing the
endpoints have the same full compact-interval weighted completion. -/
theorem bruhatCompactIntervalGroupInclusion_dense [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) :
    DenseRange (bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s) := by
  have h := bruhatCompactIntervalGroupCutoff_closure m τ hτ ν hm ha hb hab s isOpen_univ
  apply dense_iff_closure_eq.mpr
  apply eq_univ_of_univ_subset
  let J := bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s
  have hr : range (fun f : bruhatIntervalCutoffTests m I univ => J f.val) ⊆ range J := by
    rintro _ ⟨f, rfl⟩
    exact ⟨f.val, rfl⟩
  apply subset_trans _ (closure_mono hr)
  change univ ⊆ closure (range (fun f : bruhatIntervalCutoffTests m I univ => J f.val))
  rw [h]
  intro u _
  change ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ (univ : Set ℝ) → u g = 0
  exact Eventually.of_forall fun g hg => (hg (mem_univ _)).elim

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [CompactSpace K] in
/-- The physical group row over a compact abscissa interval splits by the
upper-ray indicator. Each term is the fixed space of its cutoff indicator. -/
theorem bruhatCompactInterval_physicalExact {a b : ℝ} (hab : a ≤ b) (s c : ℝ) (hc : c ≤ 0) :
    let E := Lp ℂ 2 W[a,b,s]
    let S := fun (U : Set ℝ) =>
      {f : E | (f : G → ℂ) =ᵐ[W[a,b,s]] (modulatedLog m ⁻¹' U).indicator (f : G → ℂ)}
    ∃ (L M R : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (R : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : G → ℂ) =ᵐ[W[a,b,s]]
        (modulatedLog m ⁻¹' Ici 0).indicator (f.val : G → ℂ)) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  have hnull : W[a,b,s] (modulatedLog m ⁻¹' {0}) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (modulatedCompactInterval_log_ae_ne m τ hτ ν hab s 0)
  exact lpTwo_cutoff_exact W[a,b,s] (modulatedLog m)
    ((continuous_toAdd.comp m.continuous).measurable) c hc hnull

end
end Masullo
